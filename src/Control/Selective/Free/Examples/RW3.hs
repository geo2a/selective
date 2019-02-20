{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}

module Control.Selective.Free.Examples.RW3 where

import Prelude hiding (read)
import qualified Control.Monad.State as S
import Control.Applicative ((<**>))
import Control.Selective
import Control.Selective.Free
import Data.Functor.Const
import Data.Either (partitionEithers)
import qualified Data.Map.Strict as Map

data Coyoneda f a where
    Coyoneda :: f x -> (x -> a) -> Coyoneda f a

instance Functor (Coyoneda f) where
    fmap f (Coyoneda x y) = Coyoneda x (f . y)

data RW k v a = R k (v -> a)
              | W k ((v -> v) -> a) deriving Functor

-- data RW k v a where
--     R :: k -> RW k v v
--     W :: k -> RW k v (v -> v)

instance Show k => Show (RW k v a) where
    show (R k _) = "R " ++ show k
    show (W k _) = "W " ++ show k

type Program k v a = Select (RW k v) a

-- -- | Interpret the mutable dictionary effect in 'MonadState'
-- toState :: (Ord k, S.MonadState (Map.Map k v) m) => Coyoneda (RW k v) a -> m a
-- toState (Coyoneda (R k) t) =
--     let s = S.get
--     in t <$> ((Map.!) <$> s <*> pure k)
-- toState (Coyoneda (W k) t) = do
--     s <- S.get
--     let action = \v -> S.evalState (S.put (Map.insert k v s) *> pure v) s
--     pure (t action)

-- | Interpret the mutable dictionary effect in 'MonadState'
toState :: Ord k => RW k v a -> S.State (Map.Map k v) a
toState (R k t) =
    let s = S.get
    in t <$> ((Map.!) <$> s <*> pure k)
-- toState (W k t) =
--     let s = S.get
--         action = \f s -> Map.adjust f s k
--     in action 

-- -- | Interpret a 'Program' in the state monad
-- runProgramState :: Ord k => Program k v a -> Map.Map k v -> (a, Map.Map k v)
-- runProgramState f s = S.runState (runSelect toState f) s

read :: k -> Program k v v
read k = liftSelect (R k id)

write :: k -> Program k v v -> Program k v v
write k p = p <**> liftSelect (W k id)

add :: Program String Int Int
add = let x = read "x"
          y = read "y"
          sum = (+) <$> x <*> y
          isZero = (==) <$> sum <*> pure 0
      in write "z" sum *>
         ifS isZero (write "sumIsZero" (pure 1))
                    (write "sumIsZero" (pure 0))
        --             -- *> sum

-- runExample :: Program String Int Int -> (Int, Map.Map String Int)
-- runExample prog = runProgramState prog
--     (Map.fromList [("x", -1), ("y", 1), ("sumIsZero", 0)])