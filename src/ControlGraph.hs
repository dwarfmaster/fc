
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}

-- |Module for handling generic (instruction-independent) control flow graph
module ControlGraph where
import Data.Map

class Jumpable jmp lbl | jmp -> lbl where
    nexts :: jmp -> [lbl]

-- |A control flow graph, where `ins` is the type of instructions
-- that only transfer the control flow to the next instruction,
-- `jmp` for branching instructions, `lbl` for labels and `edgs`
-- for annotation on edges
data Graph ins jmp lbl edgs = Graph (Map lbl (GraphBlock ins jmp lbl edgs))

-- |A control jump is either a jump or the end of the program
data ControlJump jmp = Jump jmp | Exit

-- |A linear set of instructions, with no incoming control flow except at
-- the beggining, and no jump except at the end
data GraphBlock ins jmp lbl edgs = GraphBlockCons ins edgs (GraphBlock ins jmp lbl edgs)
                                 | GraphBlockEnd  (ControlJump jmp)

-- |A block obtained by moving up in the ZGraph zipper
-- Cannot contain a jump, and all block except for the first one
-- have only one entry point
data UpBlock ins jmp lbl edgs = UpBlock ins edgs (UpBlock ins jmp lbl edgs)
                              | FirstBlock ins edgs

-- |A block obtained by moving down in the ZGraph zipper
-- Cannot contain a jump except the last one, and all block
-- have only one entry point
data DownBlock ins jmp lbl edgs = DownBlock ins edgs (DownBlock ins jmp lbl edgs)
                                | LastBlock jmp edgs

-- |A 'zipper' graph with control to an edge in particular,
-- allowing for easy modification
-- 
-- If we assume the ZGraph is pointing on edge e, we have :
--
-- /-------- GraphBlock ------------\
-- n1 ---> n2 -e-> n3 ---> n4 ---> n5
--         \-----/  |
--        UpBlock   |
--            \-----/
--           DownBlock
--
data ZGraph ins jmp lbl edgs = ZGraph edgs
                                      (UpBlock ins jmp lbl edgs)
                                      (DownBlock ins jmp lbl edgs)

