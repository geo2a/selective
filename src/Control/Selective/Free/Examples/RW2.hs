{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}

module Control.Selective.Free.Examples.RW2 where

import Prelude hiding (read)
import qualified Control.Monad.State as S
import Control.Selective
import Control.Selective.Free
-- import Data.Functor.Coyoneda
import Data.Functor.Const
import Data.Either (partitionEithers)
import qualified Data.Map.Strict as Map

data RW k v a = R k                 (v -> a)
              | W k (Program k v v) (v -> a)
    deriving Functor

data RW k v a = R k                 (v -> a)
              | W k (Program k v v) (v -> a)
    deriving Functor

instance Show k => Show (RW k v a) where
    show (R k _)   = "R " ++ show k
    show (W k _ _) = "W " ++ show k

type Program k v a = Select (RW k v) a

-- | Embed a 'Read' command into a 'Program'
read :: k -> Program k v v
read k = liftSelect $ R k id

-- | Embed a 'Write' command into a 'Program'
write :: k -> Program k v v -> Program k v v
write k p = liftSelect $ W k p id

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