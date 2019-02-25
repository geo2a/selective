{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}

module Control.Selective.Free.Examples.ISA.Programs where

import Prelude hiding (mod, read)
import Data.Functor (void)
import Control.Selective
import Control.Selective.Free
import Control.Selective.Free.Examples.ISA.Types
import Control.Selective.Free.Examples.ISA.Instruction

gcdProgram :: [(InstructionAddress, Instruction)]
gcdProgram = zip [0..]
    -- # Find the greatest common divisor of values in memory locations 0 and 1,
    -- # put result to the register R1
    [ (Set R0 0)
    , (Store R0 255)
    , (Load R0 1)
    -- # Test register R0 for being zero by subtracting zero
    , (Sub R0 255)
    -- # Halt if register R0 contains zero, loop otherwise
    , (JumpZero 6)
    , (Load R0 0)
    , (Mod R0 1)
    , (Load R1 1)
    , (Store R0 1)
    , (Store R1 0)
    , (Jump (-8))
    -- , Halt
    ]
