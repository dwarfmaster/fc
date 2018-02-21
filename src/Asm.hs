
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

-- |DSL to write x86_64 assembly
module Asm ( Register(..), Size(..), Sized, RValue(..), LValue, Jumpable(..)
           -- Utilities
           , getLabel, pushLabelSuffix, popLabelSuffix, assemblyAction, assemblyCode
           , assemblyToFile, anyr
           -- Sizes
           , Size8, Size16, Size32, Size64
           -- Registers
           , rax, rbx, rcx, rdx, rsi, rdi, rbp, rsp, r8,  r9,  r10,  r11,  r12,  r13,  r14,  r15
           , eax, ebx, ecx, edx, esi, edi, ebp, esp, r8d, r9d, r10d, r11d, r12d, r13d, r14d, r15d
           , ax,  bx,  cx,  dx,  si,  di,  bp,  sp,  r8w, r9w, r10w, r11w, r12w, r13w, r14w, r15w
           , al,  bl,  cl,  dl,  sil, dil, bpl, spl, r8b, r9b, r10b, r11b, r12b, r13b, r14b, r15b
           , ah,  bh,  ch,  dh
           -- AnyRegisters
           , rax', rbx', rcx',  rdx',  rsi',  rdi',  rbp',  rsp'
           , r8',  r9',  r10',  r11',  r12',  r13',  r14',  r15'
           , eax', ebx', ecx',  edx',  esi',  edi',  ebp',  esp'
           , r8d', r9d', r10d', r11d', r12d', r13d', r14d', r15d'
           , ax',  bx',  cx',   dx',   si',   di',   bp',   sp'
           , r8w', r9w', r10w', r11w', r12w', r13w', r14w', r15w'
           , al',  bl',  cl',   dl',   sil',  dil',  bpl',  spl'
           , r8b', r9b', r10b', r11b', r12b', r13b', r14b', r15b'
           , ah',  bh',  ch',   dh'
           -- Instructions
           , movb, movw, movl, movq, movabsq, movsbw, movsbl, movsbq, movswl
           , movswq, movslq, movzbw, movzbl, movzbq, movzwl, movzwq, pushq, popq
           , leab, leaw, leal, leaq, incb, incw, incl, incq, decb, decw, decl
           , decq, negb, negw, negl, negq, notb, notw, notl, notq
           , addb, addw, addl, addq, subb, subw, subl, subq, imulw, imull, imulq
           , xorb, xorw, xorl, xorq, orb, orw, orl, orq, andb, andw, andl, andq
           , idivl, divl, cltd, idivq, divq, cqto
           , sarb, sarw, sarl, sarq, shlb, shlw, shll, shlq, shrb, shrw, shrl, shrq
           , cmpb, cmpw, cmpl, cmpq, testb, testw, testl, testq
           , je, jne, jz, jnz, js, jns, jg, jge, jl, jle, ja, jae, jb, jbe
           , sete, setne, setz, setnz, sets, setns, setg, setge, setl, setle, seta, setae, setb, setbe
           , cmove, cmovne, cmovz, cmovnz, cmovs, cmovns, cmovg, cmovge
           , cmovl, cmovle, cmova, cmovae, cmovb, cmovbe
           , label, jmp, call, leave, ret
           , comment
           ) where
import Asm.Template
import Data.Int
import Data.Monoid
import Data.List
import System.IO
import Control.Monad.State.Lazy

--   ____ _                         
--  / ___| | __ _ ___ ___  ___  ___ 
-- | |   | |/ _` / __/ __|/ _ \/ __|
-- | |___| | (_| \__ \__ \  __/\__ \
--  \____|_|\__,_|___/___/\___||___/
--                                  

-- |Class for the type describing registers
class Register a where
    -- |The register name
    reg_name :: a -> String
    -- |The way the register is refered to in the generating code
    reg_ref  :: a -> String

-- |Class for type representing sizes
class Size a where
    size_bytes :: a -> Int

-- |Relation linking a type to its size
-- ie Rax has size 64, thus we define instance Sized Rax Size64
-- Using a relation instead of a type family allow for type having
-- multiple sizes
class Sized a b

-- |Regroup type designing values that can be read from, and a way to
-- represent them in the generated assembly
class RValue a where
    arg :: a -> String

-- |Regroup types that can be written to
class RValue a => LValue a

-- |Types for values that can be jumped to
class Jumpable a where
    jumpLabel :: a -> String

--  ____  _              
-- / ___|(_)_______  ___ 
-- \___ \| |_  / _ \/ __|
--  ___) | |/ /  __/\__ \
-- |____/|_/___\___||___/
--                       

$(mkSize 8)
$(mkSize 16)
$(mkSize 32)
$(mkSize 64)

--  ____            _     _                
-- |  _ \ ___  __ _(_)___| |_ ___ _ __ ___ 
-- | |_) / _ \/ _` | / __| __/ _ \ '__/ __|
-- |  _ <  __/ (_| | \__ \ ||  __/ |  \__ \
-- |_| \_\___|\__, |_|___/\__\___|_|  |___/
--            |___/                        
-- 

-- |A generic type to store all the registers, losing the information on size
data AnyRegister = forall a. (Register a, RValue a) => AnyRegister a
instance Register AnyRegister where
    reg_name (AnyRegister x) = reg_name x
    reg_ref  (AnyRegister x) = reg_ref  x
-- When using AnyRegister, we lose the compile time information on size
instance Sized AnyRegister Size8
instance Sized AnyRegister Size16
instance Sized AnyRegister Size32
instance Sized AnyRegister Size64

instance RValue AnyRegister where
    arg (AnyRegister x) = arg x
instance LValue AnyRegister
anyr :: (Register a, RValue a) => a -> AnyRegister
anyr x = AnyRegister x

$(mkRegister "rax"  64)
$(mkRegister "rbx"  64)
$(mkRegister "rcx"  64)
$(mkRegister "rdx"  64)
$(mkRegister "rsi"  64)
$(mkRegister "rdi"  64)
$(mkRegister "rbp"  64)
$(mkRegister "rsp"  64)
$(mkRegister "r8"   64)
$(mkRegister "r9"   64)
$(mkRegister "r10"  64)
$(mkRegister "r11"  64)
$(mkRegister "r12"  64)
$(mkRegister "r13"  64)
$(mkRegister "r14"  64)
$(mkRegister "r15"  64)
$(mkRegister "eax"  32)
$(mkRegister "ebx"  32)
$(mkRegister "ecx"  32)
$(mkRegister "edx"  32)
$(mkRegister "esi"  32)
$(mkRegister "edi"  32)
$(mkRegister "ebp"  32)
$(mkRegister "esp"  32)
$(mkRegister "r8d"  32)
$(mkRegister "r9d"  32)
$(mkRegister "r10d" 32)
$(mkRegister "r11d" 32)
$(mkRegister "r12d" 32)
$(mkRegister "r13d" 32)
$(mkRegister "r14d" 32)
$(mkRegister "r15d" 32)
$(mkRegister "ax"   16)
$(mkRegister "bx"   16)
$(mkRegister "cx"   16)
$(mkRegister "dx"   16)
$(mkRegister "si"   16)
$(mkRegister "di"   16)
$(mkRegister "bp"   16)
$(mkRegister "sp"   16)
$(mkRegister "r8w"  16)
$(mkRegister "r9w"  16)
$(mkRegister "r10w" 16)
$(mkRegister "r11w" 16)
$(mkRegister "r12w" 16)
$(mkRegister "r13w" 16)
$(mkRegister "r14w" 16)
$(mkRegister "r15w" 16)
$(mkRegister "al"    8)
$(mkRegister "bl"    8)
$(mkRegister "cl"    8)
$(mkRegister "dl"    8)
$(mkRegister "ah"    8)
$(mkRegister "bh"    8)
$(mkRegister "ch"    8)
$(mkRegister "dh"    8)
$(mkRegister "sil"   8)
$(mkRegister "dil"   8)
$(mkRegister "bpl"   8)
$(mkRegister "spl"   8)
$(mkRegister "r8b"   8)
$(mkRegister "r9b"   8)
$(mkRegister "r10b"  8)
$(mkRegister "r11b"  8)
$(mkRegister "r12b"  8)
$(mkRegister "r13b"  8)
$(mkRegister "r14b"  8)
$(mkRegister "r15b"  8)


--  ___       _                           
-- |_ _|_ __ | |_ ___  __ _  ___ _ __ ___ 
--  | || '_ \| __/ _ \/ _` |/ _ \ '__/ __|
--  | || | | | ||  __/ (_| |  __/ |  \__ \
-- |___|_| |_|\__\___|\__, |\___|_|  |___/
--                    |___/               

instance Sized Int8 Size8
instance RValue Int8 where
    arg i = '$' : show i
instance Sized Int16 Size16
instance RValue Int16 where
    arg i = '$' : show i
instance Sized Int32 Size32
instance RValue Int32 where
    arg i = '$' : show i
instance Sized Int64 Size64
instance RValue Int64 where
    arg i = '$' : show i


--  ____       _       _                
-- |  _ \ ___ (_)_ __ | |_ ___ _ __ ___ 
-- | |_) / _ \| | '_ \| __/ _ \ '__/ __|
-- |  __/ (_) | | | | | ||  __/ |  \__ \
-- |_|   \___/|_|_| |_|\__\___|_|  |___/
--                                      

-- |A pointer to a memory case in the RAM
data Memory = Pointer      AnyRegister Integer -- base offset
            | PointerArray AnyRegister AnyRegister Integer Integer -- base index scale offset
-- Memory can be interpreted as being of any size
instance Sized Memory Size8
instance Sized Memory Size16
instance Sized Memory Size32
instance Sized Memory Size64
instance RValue Memory where
    arg (Pointer      base             offset) =
        mconcat [ show offset, "(", arg base, ")" ]
    arg (PointerArray base index scale offset) =
        mconcat [ show offset, "(", arg base, ",", arg index, ",", show scale, ")" ]
instance LValue Memory

--   ____            _             _   _____ _               
--  / ___|___  _ __ | |_ _ __ ___ | | |  ___| | _____      __
-- | |   / _ \| '_ \| __| '__/ _ \| | | |_  | |/ _ \ \ /\ / /
-- | |__| (_) | | | | |_| | | (_) | | |  _| | | (_) \ V  V / 
--  \____\___/|_| |_|\__|_|  \___/|_| |_|   |_|\___/ \_/\_/  
--                                                           

-- |Jumping to the address stored in a value
data Star a = Star a
instance RValue a => Jumpable (Star a) where
    jumpLabel (Star rv) = mconcat ["*(", arg rv, ")"]

-- |A static label in the source code
data Label = Label String
instance Jumpable Label where
    jumpLabel (Label s) = s
instance RValue Label where
    arg (Label s) = s

--     _                  
--    / \   ___ _ __ ___  
--   / _ \ / __| '_ ` _ \ 
--  / ___ \\__ \ | | | | |
-- /_/   \_\___/_| |_| |_|
--                        

-- |A structure to efficiently concatenate string chunks
data Rope = RLeaf String | RNode Rope Rope

-- |A catamorphism (fold) for the Rope type
ropeCat :: Monoid m => (String -> m) -> Rope -> m
ropeCat f (RLeaf s) = f s
ropeCat f (RNode r1 r2) = ropeCat f r1 <> ropeCat f r2

-- |The state stored in the state monad that Asm is
data AsmState = AsmState
              { asm_rope  :: Rope     -- ^The generated assembly code string
              , asm_names :: [String] -- ^A list of prefixes for labels
              , asm_count :: Integer  -- ^A counter used to get different labels
              }
type Asm = State AsmState

-- |Add a string to the end of the generated code
addCode :: String -> Asm ()
addCode str = do
    st <- get
    let rope = asm_rope st
    put $ st { asm_rope = RNode rope (RNode (RLeaf str) (RLeaf "\n")) }

-- |Get a new label containing name in it
getLabelN :: String -> Asm String
getLabelN name = do
    st <- get
    let i   = asm_count st
    let lbl = intercalate "_" $ reverse $ show i : name : asm_names st
    put $ st { asm_count = i + 1 }
    return lbl

-- |Get a new label
getLabel :: Asm String
getLabel = getLabelN ""

-- |Add a suffix to the following generated label names
pushLabelSuffix :: String -> Asm ()
pushLabelSuffix suf = get >>= \st -> put $ st { asm_names = suf : asm_names st }

-- |Remove the last suffix added
popLabelSuffix :: Asm ()
popLabelSuffix = get >>= \st -> put $ st { asm_names = tail $ asm_names st }

-- |Assembly code to be added to the beggining of every file
beginSource :: String
beginSource = mconcat
    [ ".text\n"
    , ".globl main\n"
    ]

-- |Assembly code to be added to the end of every file
endSource :: String
endSource = ""

-- |Apply an action on the generated assembly
assemblyAction :: Monoid m => (String -> m) -> Asm a -> m
assemblyAction f asm = ropeCat f $ RNode
    (asm_rope $ snd $ runState asm (AsmState (RLeaf beginSource) [] 0))
    (RLeaf endSource)

-- |Get assembly source code
assemblyCode :: Asm a -> String
assemblyCode = assemblyAction id

-- |Write generated assembly to file
assemblyToFile :: FilePath -> Asm a -> IO ()
assemblyToFile path asm = do
    file <- openFile path WriteMode
    assemblyAction (hPutStr file) asm
    hClose file
    return ()


--  ___           _                   _   _                 
-- |_ _|_ __  ___| |_ _ __ _   _  ___| |_(_) ___  _ __  ___ 
--  | || '_ \/ __| __| '__| | | |/ __| __| |/ _ \| '_ \/ __|
--  | || | | \__ \ |_| |  | |_| | (__| |_| | (_) | | | \__ \
-- |___|_| |_|___/\__|_|   \__,_|\___|\__|_|\___/|_| |_|___/
--                                                          

-- |Helper function to add instruction without parameter
ins0 :: String -> Asm ()
ins0 = addCode

-- |Helper function to add instruction with one parameter
ins1 :: RValue a => String -> a -> Asm ()
ins1 ins v = addCode $ mconcat [ins, " ", arg v]

-- |Helper function to add instruction with two parameters
ins2 :: (RValue a, RValue b) => String -> a -> b -> Asm ()
ins2 ins v1 v2 = addCode $ mconcat [ins, " ", arg v1, " ", arg v2]

-- |Helper function for jumps
genericJump :: Jumpable a => String -> a -> Asm ()
genericJump jump dest = addCode $ mconcat [jump, " ", jumpLabel dest]

movb :: (LValue a, RValue b, Sized a Size8,  Sized b Size8 ) => a -> b -> Asm ()
movw :: (LValue a, RValue b, Sized a Size16, Sized b Size16) => a -> b -> Asm ()
movl :: (LValue a, RValue b, Sized a Size32, Sized b Size32) => a -> b -> Asm ()
movq :: (LValue a, RValue b, Sized a Size64, Sized b Size64) => a -> b -> Asm ()

movb = ins2 "movb"
movw = ins2 "movw"
movl = ins2 "movl"
movq = ins2 "movq"

movabsq :: (LValue b, Sized b Size64) => Int64 -> b -> Asm ()
movsbw :: (RValue a, LValue b, Sized a Size8,  Sized b Size16) => a -> b -> Asm ()
movsbl :: (RValue a, LValue b, Sized a Size8,  Sized b Size32) => a -> b -> Asm ()
movsbq :: (RValue a, LValue b, Sized a Size8,  Sized b Size64) => a -> b -> Asm ()
movswl :: (RValue a, LValue b, Sized a Size16, Sized b Size32) => a -> b -> Asm ()
movswq :: (RValue a, LValue b, Sized a Size16, Sized b Size64) => a -> b -> Asm ()
movslq :: (RValue a, LValue b, Sized a Size32, Sized b Size64) => a -> b -> Asm ()
movzbw :: (RValue a, LValue b, Sized a Size8,  Sized b Size16) => a -> b -> Asm ()
movzbl :: (RValue a, LValue b, Sized a Size8,  Sized b Size32) => a -> b -> Asm ()
movzbq :: (RValue a, LValue b, Sized a Size8,  Sized b Size64) => a -> b -> Asm ()
movzwl :: (RValue a, LValue b, Sized a Size16, Sized b Size32) => a -> b -> Asm ()
movzwq :: (RValue a, LValue b, Sized a Size16, Sized b Size64) => a -> b -> Asm ()
pushq :: (RValue a, Sized a Size64) => a -> Asm ()
popq :: (LValue a, Sized a Size64) => a -> Asm ()
movabsq = ins2 "movabsq"
movsbw = ins2 "movsbw"
movsbl = ins2 "movsbl"
movsbq = ins2 "movsbq"
movswl = ins2 "movswl"
movswq = ins2 "movswq"
movslq = ins2 "movslq"
movzbw = ins2 "movzbw"
movzbl = ins2 "movzbl"
movzbq = ins2 "movzbq"
movzwl = ins2 "movzwl"
movzwq = ins2 "movzwq"
pushq  = ins1 "pushq"
popq   = ins1 "popq"

leab :: (Register a, RValue a, Sized a Size8)  => Memory -> a -> Asm ()
leaw :: (Register a, RValue a, Sized a Size16) => Memory -> a -> Asm ()
leal :: (Register a, RValue a, Sized a Size32) => Memory -> a -> Asm ()
leaq :: (Register a, RValue a, Sized a Size64) => Memory -> a -> Asm ()
incb :: (LValue a, Sized a Size8)  => a -> Asm ()
incw :: (LValue a, Sized a Size16) => a -> Asm ()
incl :: (LValue a, Sized a Size32) => a -> Asm ()
incq :: (LValue a, Sized a Size64) => a -> Asm ()
decb :: (LValue a, Sized a Size8)  => a -> Asm ()
decw :: (LValue a, Sized a Size16) => a -> Asm ()
decl :: (LValue a, Sized a Size32) => a -> Asm ()
decq :: (LValue a, Sized a Size64) => a -> Asm ()
negb :: (LValue a, Sized a Size8)  => a -> Asm ()
negw :: (LValue a, Sized a Size16) => a -> Asm ()
negl :: (LValue a, Sized a Size32) => a -> Asm ()
negq :: (LValue a, Sized a Size64) => a -> Asm ()
notb :: (RValue a, Sized a Size8)  => a -> Asm ()
notw :: (RValue a, Sized a Size16) => a -> Asm ()
notl :: (RValue a, Sized a Size32) => a -> Asm ()
notq :: (RValue a, Sized a Size64) => a -> Asm ()
leab = ins2 "leab"
leaw = ins2 "leaw"
leal = ins2 "leal"
leaq = ins2 "leaq"
incb = ins1 "incb"
incw = ins1 "incw"
incl = ins1 "incl"
incq = ins1 "incq"
decb = ins1 "decb"
decw = ins1 "decw"
decl = ins1 "decl"
decq = ins1 "decq"
negb = ins1 "negb"
negw = ins1 "negw"
negl = ins1 "negl"
negq = ins1 "negq"
notb = ins1 "notb"
notw = ins1 "notw"
notl = ins1 "notl"
notq = ins1 "notq"

addb :: (RValue a, LValue b, Sized a Size8,  Sized b Size8)  => a -> b -> Asm ()
addw :: (RValue a, LValue b, Sized a Size64, Sized b Size16) => a -> b -> Asm ()
addl :: (RValue a, LValue b, Sized a Size32, Sized b Size32) => a -> b -> Asm ()
addq :: (RValue a, LValue b, Sized a Size64, Sized b Size64) => a -> b -> Asm ()
subb :: (RValue a, LValue b, Sized a Size8,  Sized b Size8)  => a -> b -> Asm ()
subw :: (RValue a, LValue b, Sized a Size16, Sized b Size16) => a -> b -> Asm ()
subl :: (RValue a, LValue b, Sized a Size32, Sized b Size32) => a -> b -> Asm ()
subq :: (RValue a, LValue b, Sized a Size64, Sized b Size64) => a -> b -> Asm ()
imulw :: (RValue a, Sized a Size16, Register b, RValue b, Sized b Size16) => a -> b -> Asm ()
imull :: (RValue a, Sized a Size32, Register b, RValue b, Sized b Size32) => a -> b -> Asm ()
imulq :: (RValue a, Sized a Size64, Register b, RValue b, Sized b Size64) => a -> b -> Asm ()
addb  = ins2 "addb"
addw  = ins2 "addw"
addl  = ins2 "addl"
addq  = ins2 "addq"
subb  = ins2 "subb"
subw  = ins2 "subw"
subl  = ins2 "subl"
subq  = ins2 "subq"
imulw = ins2 "imulw"
imull = ins2 "imull"
imulq = ins2 "imulq"

xorb :: (RValue a, LValue b, Sized a Size8,  Sized b Size8)  => a -> b -> Asm ()
xorw :: (RValue a, LValue b, Sized a Size16, Sized b Size16) => a -> b -> Asm ()
xorl :: (RValue a, LValue b, Sized a Size32, Sized b Size32) => a -> b -> Asm ()
xorq :: (RValue a, LValue b, Sized a Size64, Sized b Size64) => a -> b -> Asm ()
orb  :: (RValue a, LValue b, Sized a Size8,  Sized b Size8)  => a -> b -> Asm ()
orw  :: (RValue a, LValue b, Sized a Size16, Sized b Size16) => a -> b -> Asm ()
orl  :: (RValue a, LValue b, Sized a Size32, Sized b Size32) => a -> b -> Asm ()
orq  :: (RValue a, LValue b, Sized a Size64, Sized b Size64) => a -> b -> Asm ()
andb :: (RValue a, LValue b, Sized a Size8,  Sized b Size8)  => a -> b -> Asm ()
andw :: (RValue a, LValue b, Sized a Size16, Sized b Size16) => a -> b -> Asm ()
andl :: (RValue a, LValue b, Sized a Size32, Sized b Size32) => a -> b -> Asm ()
andq :: (RValue a, LValue b, Sized a Size64, Sized b Size64) => a -> b -> Asm ()
xorb = ins2 "xorb"
xorw = ins2 "xorw"
xorl = ins2 "xorl"
xorq = ins2 "xorq"
orb  = ins2 "orb"
orw  = ins2 "orw"
orl  = ins2 "orl"
orq  = ins2 "orq"
andb = ins2 "andb"
andw = ins2 "andw"
andl = ins2 "andl"
andq = ins2 "andq"

idivl :: (RValue a, Sized a Size16) => a -> Asm ()
divl  :: (RValue a, Sized a Size16) => a -> Asm ()
cltd  :: Asm ()
idivq :: (RValue a, Sized a Size64) => a -> Asm ()
divq  :: (RValue a, Sized a Size64) => a -> Asm ()
cqto  :: Asm ()
idivl = ins1 "idivl"
divl  = ins1 "divl"
cltd  = ins0 "cltd"
idivq = ins1 "idivq"
divq  = ins1 "divq"
cqto  = ins0 "cqto"

sarb :: (RValue a, LValue b, Sized a Size8,  Sized b Size8)  => a -> b -> Asm ()
sarw :: (RValue a, LValue b, Sized a Size16, Sized b Size16) => a -> b -> Asm ()
sarl :: (RValue a, LValue b, Sized a Size32, Sized b Size32) => a -> b -> Asm ()
sarq :: (RValue a, LValue b, Sized a Size64, Sized b Size64) => a -> b -> Asm ()
shlb :: (RValue a, LValue b, Sized a Size8,  Sized b Size8)  => a -> b -> Asm ()
shlw :: (RValue a, LValue b, Sized a Size16, Sized b Size16) => a -> b -> Asm ()
shll :: (RValue a, LValue b, Sized a Size32, Sized b Size32) => a -> b -> Asm ()
shlq :: (RValue a, LValue b, Sized a Size64, Sized b Size64) => a -> b -> Asm ()
shrb :: (RValue a, LValue b, Sized a Size8,  Sized b Size8)  => a -> b -> Asm ()
shrw :: (RValue a, LValue b, Sized a Size16, Sized b Size16) => a -> b -> Asm ()
shrl :: (RValue a, LValue b, Sized a Size32, Sized b Size32) => a -> b -> Asm ()
shrq :: (RValue a, LValue b, Sized a Size64, Sized b Size64) => a -> b -> Asm ()
sarb = ins2 "sarb"
sarw = ins2 "sarw"
sarl = ins2 "sarl"
sarq = ins2 "sarq"
shlb = ins2 "shlb"
shlw = ins2 "shlw"
shll = ins2 "shll"
shlq = ins2 "shlq"
shrb = ins2 "shrb"
shrw = ins2 "shrw"
shrl = ins2 "shrl"
shrq = ins2 "shrq"

cmpb  :: (RValue a, RValue b, Sized a Size8,  Sized b Size8)  => a -> b -> Asm ()
cmpw  :: (RValue a, RValue b, Sized a Size16, Sized b Size16) => a -> b -> Asm ()
cmpl  :: (RValue a, RValue b, Sized a Size32, Sized b Size32) => a -> b -> Asm ()
cmpq  :: (RValue a, RValue b, Sized a Size64, Sized b Size64) => a -> b -> Asm ()
testb :: (RValue a, RValue b, Sized a Size8,  Sized b Size8)  => a -> b -> Asm ()
testw :: (RValue a, RValue b, Sized a Size16, Sized b Size16) => a -> b -> Asm ()
testl :: (RValue a, RValue b, Sized a Size32, Sized b Size32) => a -> b -> Asm ()
testq :: (RValue a, RValue b, Sized a Size64, Sized b Size64) => a -> b -> Asm ()
cmpb  = ins2 "cmpb"
cmpw  = ins2 "cmpw"
cmpl  = ins2 "cmpl"
cmpq  = ins2 "cmpq"
testb = ins2 "testb"
testw = ins2 "testw"
testl = ins2 "testl"
testq = ins2 "testq"

je  :: (Jumpable a) => a -> Asm ()
jne :: (Jumpable a) => a -> Asm ()
jz  :: (Jumpable a) => a -> Asm ()
jnz :: (Jumpable a) => a -> Asm ()
js  :: (Jumpable a) => a -> Asm ()
jns :: (Jumpable a) => a -> Asm ()
jg  :: (Jumpable a) => a -> Asm ()
jge :: (Jumpable a) => a -> Asm ()
jl  :: (Jumpable a) => a -> Asm ()
jle :: (Jumpable a) => a -> Asm ()
ja  :: (Jumpable a) => a -> Asm ()
jae :: (Jumpable a) => a -> Asm ()
jb  :: (Jumpable a) => a -> Asm ()
jbe :: (Jumpable a) => a -> Asm ()
je  = genericJump "je"
jne = genericJump "jne"
jz  = genericJump "jz"
jnz = genericJump "jnz"
js  = genericJump "js"
jns = genericJump "jns"
jg  = genericJump "jg"
jge = genericJump "jge"
jl  = genericJump "jl"
jle = genericJump "jle"
ja  = genericJump "ja"
jae = genericJump "jae"
jb  = genericJump "jb"
jbe = genericJump "jbe"

sete  :: (LValue a, Sized a Size8) => a -> Asm ()
setne :: (LValue a, Sized a Size8) => a -> Asm ()
setz  :: (LValue a, Sized a Size8) => a -> Asm ()
setnz :: (LValue a, Sized a Size8) => a -> Asm ()
sets  :: (LValue a, Sized a Size8) => a -> Asm ()
setns :: (LValue a, Sized a Size8) => a -> Asm ()
setg  :: (LValue a, Sized a Size8) => a -> Asm ()
setge :: (LValue a, Sized a Size8) => a -> Asm ()
setl  :: (LValue a, Sized a Size8) => a -> Asm ()
setle :: (LValue a, Sized a Size8) => a -> Asm ()
seta  :: (LValue a, Sized a Size8) => a -> Asm ()
setae :: (LValue a, Sized a Size8) => a -> Asm ()
setb  :: (LValue a, Sized a Size8) => a -> Asm ()
setbe :: (LValue a, Sized a Size8) => a -> Asm ()
sete  = ins1 "sete"
setne = ins1 "setne"
setz  = ins1 "setz"
setnz = ins1 "setnz"
sets  = ins1 "sets"
setns = ins1 "setns"
setg  = ins1 "setg"
setge = ins1 "setge"
setl  = ins1 "setl"
setle = ins1 "setle"
seta  = ins1 "seta"
setae = ins1 "setae"
setb  = ins1 "setb"
setbe = ins1 "setbe"

cmove  :: (RValue a, LValue b, Sized a s, Sized b s) => a -> b -> Asm ()
cmovne :: (RValue a, LValue b, Sized a s, Sized b s) => a -> b -> Asm ()
cmovz  :: (RValue a, LValue b, Sized a s, Sized b s) => a -> b -> Asm ()
cmovnz :: (RValue a, LValue b, Sized a s, Sized b s) => a -> b -> Asm ()
cmovs  :: (RValue a, LValue b, Sized a s, Sized b s) => a -> b -> Asm ()
cmovns :: (RValue a, LValue b, Sized a s, Sized b s) => a -> b -> Asm ()
cmovg  :: (RValue a, LValue b, Sized a s, Sized b s) => a -> b -> Asm ()
cmovge :: (RValue a, LValue b, Sized a s, Sized b s) => a -> b -> Asm ()
cmovl  :: (RValue a, LValue b, Sized a s, Sized b s) => a -> b -> Asm ()
cmovle :: (RValue a, LValue b, Sized a s, Sized b s) => a -> b -> Asm ()
cmova  :: (RValue a, LValue b, Sized a s, Sized b s) => a -> b -> Asm ()
cmovae :: (RValue a, LValue b, Sized a s, Sized b s) => a -> b -> Asm ()
cmovb  :: (RValue a, LValue b, Sized a s, Sized b s) => a -> b -> Asm ()
cmovbe :: (RValue a, LValue b, Sized a s, Sized b s) => a -> b -> Asm ()
cmove  = ins2 "cmove"
cmovne = ins2 "cmovne"
cmovz  = ins2 "cmovz"
cmovnz = ins2 "cmovnz"
cmovs  = ins2 "cmovs"
cmovns = ins2 "cmovns"
cmovg  = ins2 "cmovg"
cmovge = ins2 "cmovge"
cmovl  = ins2 "cmovl"
cmovle = ins2 "cmovle"
cmova  = ins2 "cmova"
cmovae = ins2 "cmovae"
cmovb  = ins2 "cmovb"
cmovbe = ins2 "cmovbe"

label :: Label -> Asm ()
label (Label s) = addCode $ s ++ ":"

jmp  :: (Jumpable a) => a -> Asm ()
call :: (Jumpable a) => a -> Asm ()
jmp  = genericJump "jmp"
call = genericJump "call"

leave :: Asm ()
ret   :: Asm ()
leave = ins0 "leave"
ret   = ins0 "ret"

comment :: String -> Asm ()
comment s = addCode ('#':s)

