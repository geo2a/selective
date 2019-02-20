{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}

module Control.Selective.Free.Examples.FS where

import Prelude hiding (read)
import qualified Control.Monad.State as S
import Control.Selective
import Control.Selective.Free
-- import Data.Functor.Coyoneda
import Data.Functor.Const
import Data.Either (partitionEithers)
import qualified Data.Map.Strict as Map
data F k v a where
    R :: k -> F k v v
    W :: k -> F k v v -> F k v v

data Coyoneda f a where
    Coyoneda :: f x -> (x -> a) -> Coyoneda f a

instance Functor (Coyoneda f) where
    fmap f (Coyoneda x y) = Coyoneda x (f . y)

-- showCF :: (Show k, Show v) => Coyoneda (F k v) a -> String
-- showCF (Coyoneda (R k) t)   = "Read " ++ show k
-- showCF (Coyoneda (W k v) t) = "Write " ++ show k ++ " " ++ showCF v

-- | Coyoneda turns the effect signature into a 'Functor'
--   so the 'KVStateF' datatype may be used in Free constructions
newtype FS k v a = FS (Coyoneda (F k v) a)
    deriving Functor

showFS :: (Show k, Show v) => FS k v a -> String
showFS (FS (Coyoneda (R k) t))    = "Read " ++ show k
showFS (FS (Coyoneda (W k fv) t)) = "Write " ++ show k -- ++ " " ++ showFS fv

instance (Show k, Show v) => Show (FS k v a) where
    show x = showFS x

r :: k -> FS k v v
r k = FS $ Coyoneda (R k) id

w :: k -> FS k v a -> FS k v a
w k (FS (Coyoneda (R kk  ) y)) = FS $ Coyoneda (W k (R kk  )) y
w k (FS (Coyoneda (W kk x) y)) = FS $ Coyoneda (W k (W kk x)) y

type Program k v a = Select (FS k v) a

-- | Embed a 'Read' command into a 'Program'
read :: k -> Program k v v
read k = liftSelect (r k)

-- | Embed a 'Write' command into a 'Program'
write :: k -> Program k v v -> Program k v v
write k fv = runSelect (liftSelect . w k) fv

-- | Interpret the mutable dictionary effect in 'MonadState'
toState :: (Ord k, S.MonadState (Map.Map k v) m) => FS k v a -> m a
toState (FS (Coyoneda (R k) t)) =
    let s = S.get
    in t <$> ((Map.!) <$> s <*> pure k)
toState (FS (Coyoneda (W k fv) t)) = do
    s <- S.get
    let (v, s') = S.runState (toState (FS $ Coyoneda fv id)) s
        s'' = Map.insert k v s'
    S.put s''
    t <$> pure v

-- | Interpret a 'Program' in the state monad
runProgramState :: Ord k => Program k v a -> Map.Map k v -> (a, Map.Map k v)
runProgramState f s = S.runState (runSelect toState f) s

add :: Program String Int Int
add = let x = read "x"
          y = read "y"
          sum = (+) <$> x <*> y
        --   isZero = (==) <$> sum <*> pure 0
      in write "z" sum
         -- ifS isZero (write "sumIsZero" (pure 1))
         --            (write "sumIsZero" (pure 0)) *> sum

addAndWrite :: Program String Int Int
addAndWrite =
    let x = read "x"
        y = read "y"
        sum = (+) <$> x <*> y
    in write "z" sum

runExample :: Program String Int Int -> (Int, Map.Map String Int)
runExample prog = runProgramState prog
    (Map.fromList [("x", 5), ("y", 6), ("sumIsZero", 0)])

-- | Inspect add's effects
--   > analyseAdd
--   ([],Left (Read "y" :| [Read "x",Write "sumIsZero" 0,Write "sumIsZero" 1,Read "y",Read "x"]))
analyseAdd = analyse add
