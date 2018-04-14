
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables    #-}

-- |Module for handling generic (instruction-independent) control flow graph
-- TODO export only what's necessary
module ControlGraph where

import qualified Data.Map as M
import           Data.Map (Map)


--  ____        _          ____        __ _       _ _   _             
-- |  _ \  __ _| |_ __ _  |  _ \  ___ / _(_)_ __ (_) |_(_) ___  _ __  
-- | | | |/ _` | __/ _` | | | | |/ _ \ |_| | '_ \| | __| |/ _ \| '_ \ 
-- | |_| | (_| | || (_| | | |_| |  __/  _| | | | | | |_| | (_) | | | |
-- |____/ \__,_|\__\__,_| |____/ \___|_| |_|_| |_|_|\__|_|\___/|_| |_|
--                                                                    

class Jumpable jmp lbl | jmp -> lbl where
    nexts :: jmp -> [lbl]

-- |A control flow graph, where `ins` is the type of instructions
-- that only transfer the control flow to the next instruction,
-- `jmp` for branching instructions, `lbl` for labels and `edgs`
-- for annotation on edges
data Graph ins jmp lbl edgs = Graph (Map lbl (GraphBlock ins jmp lbl edgs))

-- |A control jump is either a jump, the end of the program
-- or an inconditionnal jump
data ControlJump ins jmp lbl edgs = Jump jmp | Exit | Continue lbl

-- |A linear set of instructions, with no incoming control flow except at
-- the beggining, and no jump except at the end
-- A graph block as necessarily at least two nodes (GraphBlockEnd encode a node
-- with a standart instruction, and an edge to a jump)
data GraphBlock ins jmp lbl edgs = GraphBlockCons ins edgs (GraphBlock ins jmp lbl edgs)
                                 | GraphBlockEnd  ins edgs (ControlJump ins jmp lbl edgs)

-- |A block obtained by moving up in the ZGraph zipper
-- Cannot contain a jump, and all block except for the first one
-- have only one entry point
data UpBlock ins jmp lbl edgs = UpBlock ins edgs (UpBlock ins jmp lbl edgs)
                              | FirstBlock ins edgs

-- |A block obtained by moving down in the ZGraph zipper
-- Cannot contain a jump except the last one, and all block
-- have only one entry point
data DownBlock ins jmp lbl edgs = DownBlock ins edgs (DownBlock ins jmp lbl edgs)
                                | LastBlock (ControlJump ins jmp lbl edgs) edgs

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
mapGB :: forall ins ins' jmp lbl edgs. 
         (ins -> ins') -> GraphBlock ins jmp lbl edgs -> GraphBlock ins' jmp lbl edgs
mapGB f (GraphBlockCons i e t)   = GraphBlockCons (f i) e $ mapGB f t
mapGB f (GraphBlockEnd i e cjmp) = GraphBlockEnd  (f i) e njmp
 where njmp :: ControlJump ins' jmp lbl edgs
       njmp = case cjmp of
                Exit       -> Exit
                Jump j     -> Jump j
                Continue l -> Continue l

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

data DownIns ins jmp lbl edgs = DownIns ins | LastIns (ControlJump ins jmp lbl edgs)
-- |Get the instruction at the end of the edge
peekDown :: ZGraph ins jmp lbl edgs -> DownIns ins jmp lbl edgs
peekDown (ZGraph _ _ (LastBlock j _  ) _ _) = LastIns j
peekDown (ZGraph _ _ (DownBlock i _ _) _ _) = DownIns i

-- |Zip the ZGraph to get back the graph
-- O(s + log n) where s is the size of the block associated with the
-- zipper graph, and n is the number of labels in the graph
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
-- O(s) where s is the size of the block associated to the label
gnexts :: forall ins jmp lbl edgs
        . (Jumpable jmp lbl, Ord lbl)
        => Graph ins jmp lbl edgs -> lbl -> Maybe [lbl]
gnexts (Graph mp) lbl = M.lookup lbl mp >>= \block ->
    return $ case getJump block of
        Exit       -> []
        Jump j     -> nexts j
        Continue l -> [l]
 where getJump :: GraphBlock ins jmp lbl edgs -> ControlJump ins jmp lbl edgs
       getJump (GraphBlockEnd  _ _ j    ) = j
       getJump (GraphBlockCons _ _ downb) = getJump downb

-- |Get the antecedents of a block
-- Returns Nothing if lbl is not the label of a node
-- O(\sum_l (s_l + d_l)) where s_l is the size of the block of label l
-- and d_l is the number of outgoing edges from block of label l
gprevs :: forall ins jmp lbl edgs
       . (Jumpable jmp lbl, Ord lbl)
      => Graph ins jmp lbl edgs -> lbl -> Maybe [lbl]
gprevs (Graph mp) label = M.lookup label mp >>= \_ ->
    return $ M.foldWithKey foldfun [] mp
 where getjump :: GraphBlock ins jmp lbl edgs -> ControlJump ins jmp lbl edgs
       getjump (GraphBlockCons _ _ nextb) = getjump nextb
       getjump (GraphBlockEnd  _ _ cj)    = cj
       isAnte :: lbl -> lbl -> GraphBlock ins jmp lbl edgs -> [lbl]
       isAnte ante lblock block = case getjump block of
           Exit            -> []
           Continue clabel -> if ante == clabel        then [lblock] else []
           Jump jmp        -> if ante `elem` nexts jmp then [lblock] else []
       foldfun :: lbl -> GraphBlock ins jmp lbl edgs -> [lbl] -> [lbl]
       foldfun key block = (++) $ isAnte label key block

-- |Create a new block in the graph, with a given label, instruction,
-- edge and jump. If no jump is given, it is set to Exit
-- If the label is already present in the graph, it fails by returning Nothing
--
-- O(log n) where n is the number of labels
addBlock :: forall ins jmp lbl edgs. Ord lbl
         => lbl -> ins -> edgs -> Maybe jmp
         -> Graph ins jmp lbl edgs
         -> Maybe (Graph ins jmp lbl edgs)
addBlock label instr edge jump (Graph mp) =
    case M.lookup label mp of
      Just _  -> Nothing
      Nothing -> Just $ Graph $ M.insert label block mp
 where block :: GraphBlock ins jmp lbl edgs
       block = GraphBlockEnd instr edge $ mkcontrol jump
       mkcontrol :: Maybe jmp -> ControlJump ins jmp lbl edgs
       mkcontrol Nothing  = Exit
       mkcontrol (Just j) = Jump j

-- |Change the label of the last edge in an UpBlock
-- O(1)
setEdgeU :: edgs -> UpBlock ins jmp lbl edgs -> UpBlock ins jmp lbl edgs
setEdgeU nedge (UpBlock instr _ upb) = UpBlock instr nedge upb
setEdgeU nedge (FirstBlock instr _)  = FirstBlock instr nedge

-- |Change the label of the first edge in a DownBlock
-- O(1)
setEdgeD :: edgs -> DownBlock ins jmp lbl edgs -> DownBlock ins jmp lbl edgs
setEdgeD nedge (DownBlock instr _ downb) = DownBlock instr nedge downb
setEdgeD nedge (LastBlock jump _)        = LastBlock jump nedge

-- |Split a block into two, at the edge focused by the zipper
-- Takes the label of the new block and a function to split the edge
-- The returned zipper graph is focused on the edge just before the
-- continue
-- Fails if label is already present in the graph
--
--                                         / i1 --e1-- Continue label
--  i1 --e-- i2 => let (e1,i3,e2) = f e in |      ^
--                                         \ label: i3 --e2-- i2
-- O(log n) where n is the number of labels
splitZ :: forall ins jmp lbl edgs. Ord lbl
       => lbl -> (edgs -> (edgs,ins,edgs))
       -> ZGraph ins jmp lbl edgs
       -> Maybe (ZGraph ins jmp lbl edgs)
splitZ nlabel f (ZGraph e i1 i2 (Graph mp) label) =
    case M.lookup nlabel mp of
        Just _  -> Nothing
        Nothing -> Just $ ZGraph e1
                                 (setEdgeU e1 i1)
                                 (LastBlock (Continue nlabel) e1)
                                 ngr
                                 label
 where (e1,i3,e2) = f e
       nblock :: GraphBlock ins jmp lbl edgs
       nblock = buildDown i3 $ setEdgeD e2 i2
       ngr :: Graph ins jmp lbl edgs
       ngr = Graph $ M.insert nlabel nblock mp

-- |Inserts an instruction and an edge after the focused instruction
-- The resulting focused edge is the new one
--
-- i1 --e-- i2 => i1 --e-- ni --ne-- i2
--      ^                       ^
-- O(1)
insertZ :: ins -> edgs
        -> ZGraph ins jmp lbl edgs
        -> ZGraph ins jmp lbl edgs
insertZ ni ne (ZGraph _ i1 i2 gr label) =
    ZGraph ne
           (UpBlock ni ne i1)
           (setEdgeD ne i2)
           gr
           label

-- |Update the previous instruction
-- O(1)
updateUpZ :: (UpIns ins jmp lbl edgs -> ins)
          -> ZGraph ins jmp lbl edgs
          -> ZGraph ins jmp lbl edgs
updateUpZ f (ZGraph e (UpBlock i _ upb) downb gr label) =
    ZGraph e (UpBlock (f $ UpIns i) e upb) downb gr label
updateUpZ f (ZGraph e (FirstBlock i _) downb gr label) =
    ZGraph e (FirstBlock (f $ FirstIns i) e) downb gr label

-- |Update the next instruction
-- Will use the right function depending on wether the next
-- instruction is a jump
-- O(1)
updateDownZ :: (ins -> ins)
            -> (ControlJump ins jmp lbl edgs -> ControlJump ins jmp lbl edgs)
            -> ZGraph ins jmp lbl edgs
            -> ZGraph ins jmp lbl edgs
updateDownZ f _ (ZGraph e upb (DownBlock i _ downb) gr label) =
    ZGraph e upb (DownBlock (f i) e downb) gr label
updateDownZ _ g (ZGraph e upb (LastBlock j _) gr label) =
    ZGraph e upb (LastBlock (g j) e) gr label

-- TODO implement an optimize function that does the following :
-- *Combine all block that are linearly linked (ie if two block are linked
-- by a Continue, and the second has only one input, combine them in only
-- one block)



--  __  __                       _   _____          _ _ _ _   _           
-- |  \/  | ___  _ __   __ _  __| | |  ___|_ _  ___(_) (_) |_(_) ___  ___ 
-- | |\/| |/ _ \| '_ \ / _` |/ _` | | |_ / _` |/ __| | | | __| |/ _ \/ __|
-- | |  | | (_) | | | | (_| | (_| | |  _| (_| | (__| | | | |_| |  __/\__ \
-- |_|  |_|\___/|_| |_|\__,_|\__,_| |_|  \__,_|\___|_|_|_|\__|_|\___||___/
--                                                                        

-- |A class for monads that have a way to get an infinite supply of always
-- different labels
class Monad m => MonadLabel m lbl | m -> lbl where
    setSeens    :: [lbl] -> m () -- ^Initialize it with a list of already used labels
    getNewLabel :: m lbl         -- ^Returns a new label

-- |A class for monads that allow to move along a zipper on a graph
class (Jumpable jmp lbl, MonadLabel m lbl)
   => MonadCGZ m ins jmp lbl edgs | m -> ins jmp lbl edgs
   where
    runCGS       :: Graph ins jmp lbl edgs -> lbl -> m a
                 -> Maybe (a, Graph ins jmp lbl edgs)
    upZM         :: m Bool -- ^Try moving up, returns False if can't
    downZM       :: m Bool -- ^Try moving down, returns False if can't
    peekZM       :: m (UpIns ins jmp lbl edgs, edgs, DownIns ins jmp lbl edgs)
    updateUpZM   :: (UpIns ins jmp lvl edgs -> ins) -> m ()
    updateDownZM :: (ins -> ins)
                 -> (ControlJump ins jmp lbl edgs -> ControlJump ins jmp lbl edgs)
                 -> m ()
    splitZM      :: (edgs -> (ins,edgs,ins)) -> m ()

-- TODO create an instance of MonadCGZ as a monad transformer

