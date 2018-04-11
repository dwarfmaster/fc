
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables    #-}

-- |Module for handling generic (instruction-independent) control flow graph
module ControlGraph where
import qualified Data.Map as M
import           Data.Map (Map)

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
-- A graph block as necessarily at least two nodes (GraphBlockEnd encode a node
-- with a standart instruction, and an edge to a jump)
data GraphBlock ins jmp lbl edgs = GraphBlockCons ins edgs (GraphBlock ins jmp lbl edgs)
                                 | GraphBlockEnd  ins edgs (ControlJump jmp)

-- |A block obtained by moving up in the ZGraph zipper
-- Cannot contain a jump, and all block except for the first one
-- have only one entry point
data UpBlock ins jmp lbl edgs = UpBlock ins edgs (UpBlock ins jmp lbl edgs)
                              | FirstBlock ins edgs

-- |A block obtained by moving down in the ZGraph zipper
-- Cannot contain a jump except the last one, and all block
-- have only one entry point
data DownBlock ins jmp lbl edgs = DownBlock ins edgs (DownBlock ins jmp lbl edgs)
                                | LastBlock (ControlJump jmp) edgs

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
                                      (Graph ins jmp lbl edgs)
                                      lbl


--  _   _ _   _ _     
-- | | | | |_(_) |___ 
-- | | | | __| | / __|
-- | |_| | |_| | \__ \
--  \___/ \__|_|_|___/
--                    

-- |Creates an empty graph
emptyGraph :: Graph ins jmp lbl edgs
emptyGraph = Graph M.empty

-- |Map over the instructions of a GraphBlock
mapGB :: (ins -> ins') -> GraphBlock ins jmp lbl edgs -> GraphBlock ins' jmp lbl edgs
mapGB f (GraphBlockCons i e t)   = GraphBlockCons (f i) e $ mapGB f t
mapGB f (GraphBlockEnd i e cjmp) = GraphBlockEnd  (f i) e cjmp

-- |Map over the instructions of a graph
mapG :: (ins -> ins') -> Graph ins jmp lbl edgs -> Graph ins' jmp lbl edgs
mapG f (Graph m) = Graph $ M.map (mapGB f) m

-- |Focus the first edge of a block
focus :: forall ins jmp lbl edgs. Ord lbl
      => Graph ins jmp lbl edgs -> lbl -> Maybe (ZGraph ins jmp lbl edgs)
focus (Graph mp) label = M.lookup label mp >>= \gb -> return $ focusGB gb

 where focusGB :: GraphBlock ins jmp lbl edgs -> ZGraph ins jmp lbl edgs
       focusGB (GraphBlockEnd instr edg jump) =
           ZGraph edg
                  (FirstBlock instr edg)
                  (LastBlock jump edg)
                  (Graph mp)
                  label
       focusGB (GraphBlockCons instr edg blocks) =
           ZGraph edg
                  (FirstBlock instr edg)
                  (zippify edg blocks)
                  (Graph mp)
                  label

       zippify :: edgs -> GraphBlock ins jmp lbl edgs
                       -> DownBlock ins jmp lbl edgs
       zippify edge (GraphBlockCons instr edg blocks) =
           DownBlock instr edge $ zippify edg blocks
       zippify edge (GraphBlockEnd instr edg jump) =
           DownBlock instr edge $ LastBlock jump edg

-- |Move the focus to the next edge
-- Returns Nothing if we're already on the last edge of the block
focusDown :: ZGraph ins jmp lbl edgs -> Maybe (ZGraph ins jmp lbl edgs)
focusDown (ZGraph _   _   (LastBlock _ _)       _  _  ) = Nothing
focusDown (ZGraph edg upb (DownBlock i e downb) gr lbl) = Just $
    ZGraph e
           (UpBlock i edg upb)
           downb
           gr
           lbl

-- |Move the focus to the previous edge
-- Returns Nothing if we're already on the first edge of the block
focusUp :: ZGraph ins jmp lbl edgs -> Maybe (ZGraph ins jmp lbl edgs)
focusUp (ZGraph _   (FirstBlock _ _)  _     _  _  ) = Nothing
focusUp (ZGraph edg (UpBlock i e upb) downb gr lbl) = Just $
    ZGraph e
           upb
           (DownBlock i edg downb)
           gr
           lbl

-- |Get the focused edge
peekEdge :: ZGraph ins jmp lbl edgs -> edgs
peekEdge (ZGraph e _ _ _ _) = e

data UpIns ins jmp lbl edgs = UpIns ins | FirstIns ins
-- |Get the instruction at the root of the edge
peekUp :: ZGraph ins jmp lbl edgs -> UpIns ins jmp lbl edgs
peekUp (ZGraph _ (FirstBlock i _  ) _ _ _) = FirstIns i
peekUp (ZGraph _ (UpBlock    i _ _) _ _ _) = UpIns    i

data DownIns ins jmp lbl edgs = DownIns ins | LastIns (ControlJump jmp)
-- |Get the instruction at the end of the edge
peekDown :: ZGraph ins jmp lbl edgs -> DownIns ins jmp lbl edgs
peekDown (ZGraph _ _ (LastBlock j _  ) _ _) = LastIns j
peekDown (ZGraph _ _ (DownBlock i _ _) _ _) = DownIns i

-- |Zip the ZGraph to get back the graph
unfocus :: forall ins jmp lbl edgs. Ord lbl
        => ZGraph ins jmp lbl edgs -> Graph ins jmp lbl edgs
unfocus (ZGraph _ upb downb (Graph mp) lbl) = Graph $ M.insert lbl newBlock mp
 where newBlock :: GraphBlock ins jmp lbl edgs
       newBlock = newBlockFrom upb downb
       newBlockFrom :: UpBlock    ins jmp lbl edgs
                    -> DownBlock  ins jmp lbl edgs
                    -> GraphBlock ins jmp lbl edgs
       newBlockFrom (FirstBlock i e) (LastBlock j _) = GraphBlockEnd i e j
       newBlockFrom (UpBlock i e up) (LastBlock j _) = buildUp up $ GraphBlockEnd i e j
       newBlockFrom (FirstBlock i _) down            = buildDown i down
       newBlockFrom (UpBlock i _ up) down            = buildUp up $ buildDown i down

       buildUp :: UpBlock    ins jmp lbl edgs
               -> GraphBlock ins jmp lbl edgs
               -> GraphBlock ins jmp lbl edgs
       buildUp (UpBlock i e up) gb = buildUp up $ GraphBlockCons i e gb
       buildUp (FirstBlock i e) gb = GraphBlockCons i e gb

       buildDown :: ins
                 -> DownBlock  ins jmp lbl edgs
                 -> GraphBlock ins jmp lbl edgs
       buildDown i (LastBlock j e)       = GraphBlockEnd i e j
       buildDown i (DownBlock i' e down) = GraphBlockCons i e $ buildDown i' down

-- |Give the blocks following the given block
-- Returns Nothing if lbl is not the label of a node
-- Is linear in the size of the block associated to the label
gnexts :: forall ins jmp lbl edgs
        . (Jumpable jmp lbl, Ord lbl)
        => Graph ins jmp lbl edgs -> lbl -> Maybe [lbl]
gnexts (Graph mp) lbl = M.lookup lbl mp >>= \block ->
    return $ case getJump block of
        Exit   -> []
        Jump j -> nexts j
 where getJump :: GraphBlock ins jmp lbl edgs -> ControlJump jmp
       getJump (GraphBlockEnd  _ _ j    ) = j
       getJump (GraphBlockCons _ _ downb) = getJump downb

-- TODO utilities to modify graph, both directly and via zipper
