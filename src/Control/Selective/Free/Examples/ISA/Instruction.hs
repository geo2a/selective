{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE LambdaCase #-}

module Control.Selective.Free.Examples.ISA.Instruction where

import Prelude hiding (div, mod, read)
import qualified Prelude (div, mod)
import Data.Functor (void)
import qualified Data.Set as Set
import Data.Maybe (fromJust)
import Control.Selective
import Control.Selective.Free
import Algebra.Graph
import Algebra.Graph.Export.Dot
import Control.Selective.Free.Examples.ISA.Types

--------------------------------------------------------------------------------
-------- Instructions ----------------------------------------------------------
--------------------------------------------------------------------------------


data Instruction where
  Halt   :: Instruction
  Load   :: Reg -> Address -> Instruction
  Set    :: Reg -> Value -> Instruction
  Store  :: Reg -> Address -> Instruction
  Add    :: Reg -> Reg -> Address -> Instruction
  Sub    :: Reg -> Reg -> Address -> Instruction
  Mul    :: Reg -> Address -> Instruction
  Div    :: Reg -> Address -> Instruction
  Mod    :: Reg -> Address -> Instruction
  Abs    :: Reg -> Instruction
  Jump :: Value -> Instruction
  JumpZero :: Value -> Instruction
  LoadMI :: Reg -> Address -> Instruction

deriving instance Show Instruction

semantics :: Instruction -> ISA Value
semantics i = case i of
    Halt            -> undefined -- halt
    Load reg addr   -> load (Register reg) (Memory addr)
    LoadMI reg addr -> undefined -- loadMI reg addr
    Set reg val     -> set (Register reg) val
    Store reg addr  -> store (Register reg) (Memory addr)
    Add reg1 reg2 addr    -> addOverflow (Register reg1) (Register reg2) (Memory addr)
    Sub reg1 reg2 addr    -> sub (Register reg1) (Register reg2) (Memory addr)
    Mul reg addr    -> mul (Register reg) (Memory addr)
    Div reg addr    -> div (Register reg) (Memory addr)
    Mod reg addr    -> mod (Register reg) (Memory addr)
    Abs reg         -> undefined -- abs (Register reg)
    Jump simm8      -> jump simm8
    JumpZero simm8  -> jumpZero simm8

------------
-- Set -----
------------

set :: Key -> Value -> ISA Value
set reg = write reg . pure

-------------
-- Load -----
-------------

load :: Key -> Key -> ISA Value
load reg addr = write reg (read addr)

--------------
-- Store -----
--------------

store :: Key -> Key -> ISA Value
store reg addr = write addr (read reg)

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
addNaive :: Key -> Key -> Key -> ISA Value
addNaive reg1 reg2 reg3 =
    let sum = (+) <$> read reg1 <*> read reg2
        isZero = (==) <$> sum <*> pure 0
    in write (Flag Zero) (ifS isZero (pure 1) (pure 0))
       *> write reg3 sum

-- | This implementations of 'add' executes the effects associated with the 'sum' value only once and
--   then wires the pure value into the computations which require it without triggering the effects again.
--
--   > analyse add
--   ([],Left (W "zero" :| [W "z",R "y",R "x"]))
--
add :: Key -> Key -> Key -> ISA Value
add reg1 reg2 reg3 =
    let x = read reg1
        y = read reg2
        sum = (+) <$> x <*> y
        isZero = (==) <$> pure 0 <*> write reg3 sum
    in write (Flag Zero) (fromBool <$> isZero)

-- -- | This is a fully inlined version of 'add'
-- addNormalForm :: ISA Value
-- addNormalForm =
--     write "zero" (ifS ((==) <$> pure 0 <*> write "z" ((+) <$> read "x" <*> read "y")) (pure 1) (pure 0))

-- addState :: Memory
-- addState =
--     Map.fromList [ ("x", 255)
--                  , ("y", 1)
--                  , ("zero", 0)
--                  , ("overflow", 0)
--                  , ("ic", 0)
--                  ]

-----------------
-- jumpZero -----
-----------------
jumpZero :: Value -> ISA Value
jumpZero offset =
    let pc       = read PC
        zeroSet  = (/=) <$> pure 0 <*> read (Flag Zero)
        -- modifyPC = void $ write PC (pure offset) -- (fmap (+ offset) pc)
        modifyPC = void $ write PC (fmap (+ offset) pc)
    in whenS zeroSet modifyPC *> pure offset

-- | Unconditional jump.
jump :: Value -> ISA Value
jump simm =
    write PC (fmap ((+) $ simm) (read PC))

-- jumpZeroMemory :: Map.Map Key Value
-- jumpZeroMemory =
--     Map.fromList [ ("ic", 0)
--                  , ("zero", 0)
--                  ]

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
addOverflow :: Key -> Key -> Key -> ISA Value
addOverflow var1 var2 dest =
    let arg1     = read var1
        arg2     = read var2
        result   = (+)  <$> arg1   <*> arg2
        isZero   = (==) <$> pure 0 <*> write dest result
        overflow = willOverflowPure <$> arg1 <*> arg2
    in write (Flag Zero)     (fromBool <$> isZero) *>
       write (Flag Overflow) (fromBool <$> overflow)

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
addOverflowNaive :: Key -> Key -> Key -> ISA Value
addOverflowNaive var1 var2 dest =
    let arg1   = read var1
        arg2   = read var2
        result = (+) <$> arg1 <*> arg2
        isZero = (==) <$> pure 0 <*> write dest result
        overflow = willOverflow arg1 arg2
    in write (Flag Zero)     (fromBool <$> isZero) *>
       write (Flag Overflow) (fromBool <$> overflow)

willOverflow :: ISA Value -> ISA Value -> ISA Bool
willOverflow arg1 arg2 =
    let o1 = (>) <$> arg2 <*> pure 0
        o2 = (>) <$> arg1 <*> ((-) <$> pure maxBound <*> arg2)
        o3 = (<) <$> arg2 <*> pure 0
        o4 = (<) <$> arg1 <*> ((-) <$> pure minBound <*> arg2)
    in  (||) <$> ((&&) <$> o1 <*> o2)
             <*> ((&&) <$> o3 <*> o4)

----------------------------------------------------------------------------------------------------

-- | Subtraction
--   NOTE: currently always sets the 'Overflow' flag to zero
sub :: Key -> Key -> Key -> ISA Value
sub var1 var2 dest =
    let arg1     = read var1
        arg2     = read var2
        result   = (-)  <$> arg1   <*> arg2
        isZero   = (==) <$> pure 0 <*> write dest result
    in write (Flag Zero)     (fromBool <$> isZero) *>
       write (Flag Overflow) (pure 0)

-- | Multiply a value from memory location to one in a register.
--   Applicative.
mul :: Key -> Key -> ISA Value
mul reg addr =
    let result = (*) <$> read reg <*> read addr
    in  write (Flag Zero) (fromBool . (== 0) <$> write reg result)

div :: Key -> Key -> ISA Value
div reg addr =
    let result = Prelude.div <$> read reg <*> read addr
    in  write (Flag Zero) (fromBool . (== 0) <$> write reg result)

mod :: Key -> Key -> ISA Value
mod reg addr =
    let result = Prelude.mod <$> read reg <*> read addr
    in  write (Flag Zero) (fromBool . (== 0) <$> write reg result)

--------------------------------------------------------------------------------

partition :: [RW a] -> ([Key], [Key])
partition = foldl go ([], [])
    where go (accR, accW) = \case (R k _)   -> (k : accR, accW)
                                  (W k _ _) -> (accR, k : accW)

-- | Compute static data flow graph of an instruction.
instructionGraph :: (InstructionAddress, Instruction)
                    -> Graph (Either Key (InstructionAddress, Instruction))
instructionGraph instrInfo@(_, instr) =
    let (ins, outs) = partition $ getEffects (semantics instr)
    in overlay (star (Right instrInfo) (map Left outs))
               (transpose $ star (Right instrInfo) (map Left ins))

-- -- | Compute static data flow graph of a program.
-- programGraph :: Program
--                  -> Graph (Either String (InstructionAddress, Instruction))
-- programGraph p = foldl go empty (map instructionGraph p)
--     where go acc g = overlay acc g
--------------------------------------------------------------------------------

-- | Serialise data flow graph as a .dot string
-- drawGraph :: Graph (Either String (InstructionAddress, Instruction)) -> String
drawGraph :: Graph (Either Key (InstructionAddress, Instruction)) -> String
drawGraph g =
    let g' = stringifyVertex <$> g
        names = vertexSet g'
        style = defaultStyleViaShow
            { vertexName = \v -> "v" ++ show (fromJust $ Set.lookupIndex v names)
            , vertexAttributes = \x -> case x of
                Left  k -> [ "shape"  := "circle"
                           , "label"  := k ]
                Right i -> [ "shape" := "record"
                           , "label" := i ] }
    in export style g'
    where
        stringifyVertex :: Either Key (InstructionAddress, Instruction) ->
                           Either String String
        stringifyVertex (Left k)       = Left  (show k)
        stringifyVertex (Right (a, i)) = Right $ show a <> "|" <> show i