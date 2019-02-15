{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}

module Control.Selective.Free.Examples.KVState where

import Prelude hiding (read)
import qualified Control.Monad.State as S
import Control.Selective
import Control.Selective.Free
import Data.Functor.Coyoneda
import qualified Data.Map.Strict as Map

-- | Signature of a mutable dictionary effect comprises two commands:
--   - 'Read k' reads the value of a key
--   - 'Write k v' updates the value of a key
data KVState k v a where
    Read  :: k -> KVState k v v
    Write :: k -> v -> KVState k v ()

deriving instance (Show k, Show v, Show a) => Show (KVState k v a)

-- | Coyoneda turns the effect signature into a 'Functor'
--   so the 'KVStateF' datatype may be used in Free constructions
newtype KVStateF k v a = KVStateF (Coyoneda (KVState k v) a)
    deriving (Functor)

-- instance (Show k, Show v, Show a) => Show (KVStateF k v a) where
--     show (KVStateF (Coyoneda t f)) = show f

-- | Interpret the mutable dictionary effect in 'MonadState'
toState :: (Ord k, S.MonadState (Map.Map k v) m) => KVStateF k v a -> m a
toState (KVStateF (Coyoneda t (Read k))) = let s = S.get
                                           in t <$> ((Map.!) <$> s <*> pure k)
toState (KVStateF (Coyoneda t (Write k v))) = do
    s' <- Map.insert k v <$> S.get
    t <$> S.put s'

-- | A 'Program' is a free selective functor over the functor 'KVStateF'
type Program k v a = Select (KVStateF k v) a

-- | Embed a 'Read' command into a 'Program'
read :: k -> Program k v v
read k = liftSelect (KVStateF $ Coyoneda id (Read k))

-- | Embed a 'Write' command into a 'Program'
write :: k -> v -> Program k v ()
write k v = liftSelect (KVStateF $ Coyoneda id (Write k v))

-- | Interpret a 'Program' in the state monad
runProgramState :: Ord k => Program k v a -> Map.Map k v -> (a, Map.Map k v)
runProgramState f s = S.runState (runSelect toState f) s

----------------------- Exampels -----------------------------------------------

-- | Add two numbers. If the sum is zero, put '1' into the "sumIsZero" variable
add :: Program String Int Int
add = let x = read "x"
          y = read "y"
          sum = (+) <$> x <*> y
          isZero = (==) <$> sum <*> pure 0
      in ifS isZero (write "sumIsZero" 1)
                    (write "sumIsZero" 0) *>
         sum

runAdd :: (Int, Map.Map String Int)
runAdd = runProgramState add (Map.fromList [("x", -1), ("y", 1), ("sumIsZero", 0)])
