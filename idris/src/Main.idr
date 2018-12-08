
module Main

import Frontend.Kotlin.Parser
import Frontend.Kotlin.AST
import Frontend.Kotlin.PrettyPrinter
import Tools.Annotation
import Lightyear.Strings
import Lightyear.Position
import System

main : IO ()
main = do
  args <- getArgs
  case args of
    [_,file] => do fl <- readFile file
                   case fl of
                     Left errmsg => putStrLn $ "Couldn't open " ++ file ++ " : ?"
                     Right syn   => do
                       putStrLn $ "Reading : " ++ syn
                       case parse fileP syn of
                         Left errmsg => do putStrLn $ "Syntax error " ++ errmsg
                                           exit 1
                         Right ast   => putStrLn $ prettyPrintAST FileTy 0 ast
    _        => do putStrLn "usage : program file.kt"
                   exit 1

