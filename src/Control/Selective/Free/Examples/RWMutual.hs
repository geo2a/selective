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
import Data.Word (Word8)
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

type Address = String

type Value   = Word8

runProgram :: Program Address v a -> Map.Map Address v -> (a, Map.Map Address v)
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
addNaive :: Program Address Value Value
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
add :: Program Address Value Value
add = let x = read "x"
          y = read "y"
          sum = (+) <$> x <*> y
          isZero = (==) <$> pure 0 <*> write "z" sum
      in write "zero" (ifS isZero (pure 1) (pure 0))

-- | This is a fully inlined version of 'add'
addNormalForm :: Program Address Value Value
addNormalForm =
    write "zero" (ifS ((==) <$> pure 0 <*> write "z" ((+) <$> read "x" <*> read "y")) (pure 1) (pure 0))

addMemory :: Map.Map Address Value
addMemory =
    Map.fromList [ ("x", 255)
                 , ("y", 1)
                 , ("zero", 0)
                 , ("overflow", 0)
                 , ("ic", 0)
                 ]

-----------------
-- jumpZero -----
-----------------

jumpZero :: Value -> Program Address Value ()
jumpZero offset =
    let ic = read "ic"
        zeroSet = (/=) <$> pure 0 <*> read "zero"
    in whenS zeroSet (void $ write "ic" (fmap (+ offset) ic))

jumpZeroMemory :: Map.Map Address Value
jumpZeroMemory =
    Map.fromList [ ("ic", 0)
                 , ("zero", 0)
                 ]

-----------------------------------
-- Add with overflow tracking -----
-----------------------------------

{-  The following example will demonstrate how important it is to be aware of your effects.

    Problem: implement the semantics of add instruction which would calculate the sum and write it
    to the specified destination, update the 'zero' flag if the sum was zero, and also detect if
    integer overflow happened and update the 'overflow' flag accordingly.

    We'll take a look at two approaches that implement this semantics and see the crucial deference
    between them.
-}

-- | Add two values and detect integer overflow
-- The interesting bit here is the call to the 'willOverflowPure' function. Since the function is
-- pure, the call 'willOverflowPure <$> arg1 <*> arg2' triggers only one 'read' of 'arg1' and 'arg2',
-- even though we use the variables many times in the 'willOverflowPure' implementation.
--
--  > analyse (addOverflow  "x" "y" "z")
--  ([],Left (W "overflow" :| [R "y",R "x",W "zero",W "z",R "y",R "x"]))
--
-- Thus, 'willOverflowPure' might be though as a atomic microcommand in some sense.
addOverflow :: Address -> Address -> Address -> Program Address Value ()
addOverflow var1 var2 dest =
    let arg1   = read var1
        arg2   = read var2
        result = (+) <$> arg1 <*> arg2
        isZero = (==) <$> pure 0 <*> write dest result
        overflow = willOverflowPure <$> arg1 <*> arg2
    in whenS isZero (void $ write "zero" (pure 1))
       *>
       whenS overflow (void $ write "overflow" (pure 1))

willOverflowPure :: Value -> Value -> Bool
willOverflowPure arg1 arg2 =
    let o1 = (>) arg2 0
        o2 = (>) arg1((-) maxBound arg2)
        o3 = (<) arg2 0
        o4 = (<) arg1((-) minBound arg2)
    in  (||) ((&&) o1 o2)
             ((&&) o3 o4)

-- | Add two values and detect integer overflow
--  In this implementations we take a different approach and, when implementing overflow detection,
--  lift all the pure operations into Applicative. This forces the semantics to read the input
--  variables more times than 'addOverflow' does (var1 3x times and var2 5x times)
--
--  > analyse (addOverflowNaive  "x" "y" "z")
--  ([],Left (W "overflow" :| [R "y",R "x",R "y",R "y",R "x",R "y",W "zero",W "z",R "y",R "x"]))
--
--  It is not clear at the moment what to do with that. Should we avoid this style? Or could it be
--  sometimes useful?
addOverflowNaive :: Address -> Address -> Address -> Program Address Value ()
addOverflowNaive var1 var2 dest =
    let arg1   = read var1
        arg2   = read var2
        result = (+) <$> arg1 <*> arg2
        isZero = (==) <$> pure 0 <*> write dest result
        overflow = willOverflow arg1 arg2
    in whenS isZero (void $ write "zero" (pure 1))
       *>
       whenS overflow (void $ write "overflow" (pure 1))

willOverflow :: Program Address Value Value -> Program Address Value Value -> Program Address Value Bool
willOverflow arg1 arg2 =
    let o1 = (>) <$> arg2 <*> pure 0
        o2 = (>) <$> arg1 <*> ((-) <$> pure maxBound <*> arg2)
        o3 = (<) <$> arg2 <*> pure 0
        o4 = (<) <$> arg1 <*> ((-) <$> pure minBound <*> arg2)
    in  (||) <$> ((&&) <$> o1 <*> o2)
             <*> ((&&) <$> o3 <*> o4)
