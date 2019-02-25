{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}

module Control.Selective.Free.Examples.ISA.Types where

import Prelude hiding (read)
import Data.Word (Word8)
import Data.Int (Int16)
import Data.Functor (void)
import qualified Control.Monad.State as S
import Control.Selective
import Control.Selective.Free
import qualified Data.Map.Strict as Map

-- | Hijack mtl's MonadState constraint to include Selective
type MonadState s m = (Selective m, S.MonadState s m)

fromBool :: Num a => Bool -> a
fromBool True  = 1
fromBool False = 0

--------------------------------------------------------------------------------
-------- Types -----------------------------------------------------------------
--------------------------------------------------------------------------------

-- | The ISA operates signed 16-bit words
type Value = Int16

-- | The ISA has 4 registers
data Reg = R0 | R1 | R2 | R3
    deriving (Show, Eq, Ord)

r0, r1, r2, r3 :: Key
[r0, r1, r2, r3] = map Register [R0, R1, R2, R3]
_ = undefined

type RegisterBank = Map.Map Reg Value

-- | The address space is indexed by one byte
type Address = Word8

-- | We model memory as a map from bytes to signed 16-bit words
type Memory = Map.Map Address Value

-- | The ISA has two flags
data F = Zero     -- ^ tracks if the result of the last arithmetical operation was zero
       | Overflow -- ^ tracks integer overflow
    deriving (Show, Eq, Ord)

type Flags = Map.Map F Value

-- | Address in the program memory
type InstructionAddress = Value

data Key =
    Register Reg
    | Memory Address
    | Flag   F
    | PC
    deriving (Eq)

instance Show Key where
    show (Register r ) = show r
    show (Memory addr) = show addr
    show (Flag   f)    = show f
    show PC            = "PC"

data ISAState = ISAState { registers :: RegisterBank
                         , memory    :: Memory
                         , pc        :: InstructionAddress
                         , flags     :: Flags
                         }

data RW a = R Key             (Value -> a)
          | W Key (ISA Value) (Value -> a)
    deriving Functor

type ISA a = Select RW a

instance Show a => Show (RW a) where
    show (R k _)   = "Read "  ++ show k
    show (W k (Pure v) _) = "Write " ++ show k ++ " " ++ show v
    show (W k _        _) = "Write " ++ show k

-- | Interpret the internal ISA effect in 'MonadState'
toState :: MonadState ISAState m => RW a -> m a
toState (R k t) = t <$> case k of
    Register r  -> (Map.!) <$> (registers <$> S.get) <*> pure r
    Memory addr -> (Map.!) <$> (memory    <$> S.get) <*> pure addr
    Flag f      -> (Map.!) <$> (flags     <$> S.get) <*> pure f
    PC          -> pc <$> S.get
toState (W k p t) = case k of
    Register r  -> do v <- runSelect toState p
                      let regs' s = Map.insert r v (registers s)
                      S.state (\s -> (t v, s {registers = regs' s}))
    Memory addr -> do v <- runSelect toState p
                      let mem' s = Map.insert addr v (memory s)
                      S.state (\s -> (t v, s {memory = mem' s}))
    Flag f      -> do v <- runSelect toState p
                      let flags' s = Map.insert f v (flags s)
                      S.state (\s -> (t v, s {flags = flags' s}))
    PC          -> error "toState: Can't write the Program Counter (PC)"


-- | Interpret a 'Program' in the state monad
runProgram :: ISA a -> ISAState -> (a, ISAState)
runProgram f s = S.runState (runSelect toState f) s

read :: Key -> ISA Value
read k = liftSelect (R k id)

write :: Key -> ISA Value -> ISA Value
write k p = p *> liftSelect (W k p id)

