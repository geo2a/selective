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

r :: k -> Coyoneda (F k v) v
r k = Coyoneda (R k) id

w :: k -> Coyoneda (F k v) a -> Coyoneda (F k v) a
w k (Coyoneda (R kk  ) y) = Coyoneda (W k (R kk  )) y
w k (Coyoneda (W kk x) y) = Coyoneda (W k (W kk x)) y

type Program k v a = Select (Coyoneda (F k v)) a

-- | Embed a 'Read' command into a 'Program'
read :: k -> Program k v v
read k = liftSelect (r k)

-- | Embed a 'Write' command into a 'Program'
write :: k -> Program k v v -> Program k v v
write k = runSelect (liftSelect . w k)

-- | Interpret the mutable dictionary effect in 'MonadState'
toState :: (Ord k, S.MonadState (Map.Map k v) m) => Coyoneda (F k v) a -> m a
toState ((Coyoneda (R k) t)) =
    let s = S.get
    in t <$> ((Map.!) <$> s <*> pure k)
toState ((Coyoneda (W k fv) t)) = do
    s <- S.get
    let (v, s') = S.runState (toState (Coyoneda fv id)) s
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
          isZero = (==) <$> sum <*> pure 0
      in ifS isZero (write "sumIsZero" (pure 1))
                    (write "sumIsZero" (pure 0)) *> sum

runAdd :: (Int, Map.Map String Int)
runAdd = runProgramState add (Map.fromList [("x", -1), ("y", 1), ("sumIsZero", 0)])

-- | Inspect add's effects
--   > analyseAdd
--   ([],Left (Read "y" :| [Read "x",Write "sumIsZero" 0,Write "sumIsZero" 1,Read "y",Read "x"]))
analyseAdd = analyse add
