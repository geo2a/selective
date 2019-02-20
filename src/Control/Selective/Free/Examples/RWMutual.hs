{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}

module Control.Selective.Free.Examples.RWMutual where

import Prelude hiding (read)
import Data.Functor (void)
import qualified Control.Monad.State as S
import Control.Selective
import Control.Selective.Free
import qualified Data.Map.Strict as Map

-- | Hijack mtl's MonadState constraint to include Selective
type MonadState s m = (Selective m, S.MonadState s m)

data RW k v a = R k                 (v -> a)
              | W k (Program k v v) (v -> a)
    deriving Functor

type Program k v a = Select (RW k v) a

instance Show k => Show (RW k v a) where
    show (R k _)   = "R " ++ show k
    show (W k _ _) = "W " ++ show k

-- | Interpret the mutable dictionary effect in 'MonadState'
toState :: (Ord k, MonadState (Map.Map k v) m) => RW k v a -> m a
toState (R k t) =
    t <$> ((Map.!) <$> S.get <*> pure k)
toState (W k p t) = do
    v <- runSelect toState p
    S.state (\s -> (t v, Map.insert k v s))

-- | Interpret a 'Program' in the state monad
runProgramState :: Ord k => Program k v a -> Map.Map k v -> (a, Map.Map k v)
runProgramState f s = S.runState (runSelect toState f) s

read :: k -> Program k v v
read k = liftSelect (R k id)

write :: k -> Program k v v -> Program k v v
write k p = p *> liftSelect (W k p id)

--------------------------------------------------------------------------------
-------- Instructions ----------------------------------------------------------
--------------------------------------------------------------------------------

runProgram :: Program String Int a -> Map.Map String Int -> (a, Map.Map String Int)
runProgram prog memory = runProgramState prog memory

------------
-- Add -----
------------

-- | Read the values of the variables "x" and "y" and write the sum into the variable "z".
--   If the sum is zero, write 1 into the variable "zero", otherwise put 0 there.
--
--   This implementation looks intuitive, but it is wrong, since the two write operations
--   can be considered independent and the effects required for computing the sum, i.e.
--   'read "x" <*> read "y"' will be executed twice. Consequently:
--   * the value written into the "z" variable is not guaranteed to be the same as the one which was
--     compared to zero,
--   * the static analysis of the computations reports more dependencies then one might have
--     naively expected
--
--     > analyse addNaive
--     ([],Left (W "z" :| [R "y",R "x",W "zero",R "y",R "x"]))
--
--     Here, the two instances of 'sum' cause the duplication of 'R "x"' and R '"y"' effects.
addNaive :: Program String Int Int
addNaive = let sum = (+) <$> read "x" <*> read "y"
               isZero = (==) <$> sum <*> pure 0
           in write "zero" (ifS isZero (pure 1) (pure 0))
              *> write "z" sum

-- | This implementations of 'add' executes the effects associated with the 'sum' value only once and
--   then wires the pure value into the computations which require it without triggering the effects again.
--
--   > analyse add
--   ([],Left (W "zero" :| [W "z",R "y",R "x"]))
--
add :: Program String Int Int
add = let x = read "x"
          y = read "y"
          sum = (+) <$> x <*> y
          isZero = (==) <$> pure 0 <*> write "z" sum
      in write "zero" (ifS isZero (pure 1) (pure 0))

-- | This is a fully inlined version of 'add'
addNormalForm :: Program String Int Int
addNormalForm =
    write "zero" (ifS ((==) <$> pure 0 <*> write "z" ((+) <$> read "x" <*> read "y")) (pure 1) (pure 0))

addMemory :: Map.Map String Int
addMemory =
    Map.fromList [ ("x", 2)
                 , ("y", 2)
                 , ("zero", 0)
                 , ("ic", 0)
                 ]

-----------------
-- jumpZero -----
-----------------

jumpZero :: Int -> Program String Int ()
jumpZero offset =
    let ic = read "ic"
        zeroSet = (/=) <$> pure 0 <*> read "zero"
    in whenS zeroSet (void $ write "ic" (fmap (+ offset) ic))

jumpZeroMemory :: Map.Map String Int
jumpZeroMemory =
    Map.fromList [ ("ic", 0)
                 , ("zero", 0)
                 ]
