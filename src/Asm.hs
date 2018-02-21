
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}

-- |DSL to write x86_64 assembly
module Asm where
import Asm.Template

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

type AnyRegister = forall a. Register a => a
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

