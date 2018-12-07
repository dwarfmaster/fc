
module Frontend.Kotlin.Parser

import Frontend.Kotlin.AST
import Frontend.Kotlin.PrettyPrinter
import Tools.Annotation
import Lightyear.Core
import Lightyear.Char
import Lightyear.Strings
import Lightyear.Combinators
import Lightyear.Position


--  __  __ _           ---------------------------------------------------------
-- |  \/  (_)___  ___  ---------------------------------------------------------
-- | |\/| | / __|/ __| ---------------------------------------------------------
-- | |  | | \__ \ (__  ---------------------------------------------------------
-- |_|  |_|_|___/\___| ---------------------------------------------------------
--                     ---------------------------------------------------------

TypePos      : Type
VarPos       : Type
ParamPos     : Type
ParamCPos    : Type
ClassPos     : Type
FunPos       : Type
DeclPos      : Type
FilePos      : Type
ExprPos      : Type
BlockPos     : Type
BlockExprPos : Type
AccessPos    : Type
TypePos      = SyntaxAnn TypeTy      Position
VarPos       = SyntaxAnn VarTy       Position
ParamPos     = SyntaxAnn ParamTy     Position
ParamCPos    = SyntaxAnn ParamCTy    Position
ClassPos     = SyntaxAnn ClassTy     Position
FunPos       = SyntaxAnn FunTy       Position
DeclPos      = SyntaxAnn DeclTy      Position
FilePos      = SyntaxAnn FileTy      Position
ExprPos      = SyntaxAnn ExprTy      Position
BlockPos     = SyntaxAnn BlockTy     Position
BlockExprPos = SyntaxAnn BlockExprTy Position
AccessPos    = SyntaxAnn AccessTy    Position

total filterMap : (a -> Maybe b) -> List a -> List b
filterMap f []       = []
filterMap f (h :: t) = case f h of
                            Just x  => x :: filterMap f t
                            Nothing => filterMap f t


--  ____              _              -------------------------------------------
-- / ___| _   _ _ __ | |_ __ ___  __ -------------------------------------------
-- \___ \| | | | '_ \| __/ _` \ \/ / -------------------------------------------
--  ___) | |_| | | | | || (_| |>  <  -------------------------------------------
-- |____/ \__, |_| |_|\__\__,_/_/\_\ -------------------------------------------
--        |___/                      -------------------------------------------

ident : Parser String
ident = do
  h <- letter
  t <- many alphaNum
  pure $ pack $ h :: t

data KeyWord = CLASS | DATA | ELSE | FALSE | FUN
             | IF | NULL | RETURN | THIS | TRUE
             | VAL | VAR | WHILE

Eq KeyWord where
  CLASS  == CLASS  = True
  DATA   == DATA   = True
  ELSE   == ELSE   = True
  FALSE  == FALSE  = True
  FUN    == FUN    = True
  IF     == IF     = True
  NULL   == NULL   = True
  RETURN == RETURN = True
  THIS   == THIS   = True
  TRUE   == TRUE   = True
  VAL    == VAL    = True
  VAR    == VAR    = True
  WHILE  == WHILE  = True
  _      == _      = False

Show KeyWord where
  show CLASS  = "class"
  show DATA   = "data"
  show ELSE   = "else"
  show FALSE  = "false"
  show FUN    = "fun"
  show IF     = "if"
  show NULL   = "null"
  show RETURN = "return"
  show THIS   = "this"
  show TRUE   = "true"
  show VAL    = "val"
  show VAR    = "var"
  show WHILE  = "while"

keyword : KeyWord -> Parser ()
keyword kw = do
  id <- ident
  case parseKey id of
       Nothing => fail $ "Expected " ++ show kw ++ ", got " ++ id
       Just k  => if k == kw then pure ()
                             else fail $ "Expected " ++ show kw ++ ", got " ++ id
 where parseKey : String -> Maybe KeyWord
       parseKey s = List.lookup s
                    [ ("class"  , CLASS  )
                    , ("data"   , DATA   )
                    , ("else"   , ELSE   )
                    , ("false"  , FALSE  )
                    , ("fun"    , FUN    )
                    , ("if"     , IF     )
                    , ("null"   , NULL   )
                    , ("return" , RETURN )
                    , ("this"   , THIS   )
                    , ("true"   , TRUE   )
                    , ("val"    , VAL    )
                    , ("var"    , VAR    )
                    , ("while"  , WHILE  )
                    ]

bit : Parser (Fin 2)
bit = do
  c <- satisfy (\x => x == '0' || x == '1')
  pure $ if c == '0' then FZ else FS (FZ)

hex : Parser (Fin 16)
hex = do
  dg <- map (ord . toUpper) hexDigit
  let val = if dg <= ord '9' then dg - ord '0' else 10 + dg - ord 'A'
  case integerToFin (cast val) 16 of
       Just fin => pure fin
       Nothing  => fail $ "Impossible : hex digit greater than 15 !"

combine : Parser a -> Parser b -> Parser (Either a b)
combine leftP rightP = (Left <$> leftP) <|> (Right <$> rightP) 

valueInBase : (n : Integer) -> (Parser (Fin $ fromInteger n)) -> Parser Integer
valueInBase base digitP = do
  msd <- digitP
  tl  <- many (combine digitP (char '_'))
  let digits = msd :: filterMap extractLeft tl
  pure $ foldl (\val => \e => val * base + finToInteger e) 0 digits
 where extractLeft : Either a b -> Maybe a
       extractLeft (Left x)  = Just x
       extractLeft (Right _) = Nothing

number : Parser Integer
number = ((string "0X" <|> string "0x") >! valueInBase 16 hex)
    <|>| ((string "0B" <|> string "0b") >! valueInBase  2 bit)
    <|>| valueInBase 10 digit

car : Parser String
car = string "\\\\"
 <|>| string "\\\""
 <|>| string "\\n"
 <|>| string "\\t"
 <|>| do c <- anyChar
         guard (ord c >= 32 && ord c <= 126 && c /= '\\' && c /= '"')
         pure $ singleton c

string : Parser String
string = concat <$> between (char '"') (char '"') (many car)

mutual
  commentStarString : Parser ()
  commentStarString = (skip $ string "*/")
                 <|>| (commentStar >>= \_ => commentStarString)
                 <|>| (anyChar >>= \_ => commentStarString)
  
  commentStar : Parser ()
  commentStar = string "/*" >! commentStarString

mutual
  commentLineString : Parser ()
  commentLineString = (skip $ endOfLine)
                 <|>| (anyChar >>= \_ => commentLineString)

  commentLine : Parser ()
  commentLine = string "//" >! commentLineString


comment : Parser ()
comment = commentStar <|>| commentLine

white : Parser ()
white = skip $ many $ (skip $ oneOf " \t\n") <|>| comment


--  _____                   ____                           ---------------------
-- |_   _|   _ _ __   ___  |  _ \ __ _ _ __ ___  ___ _ __  ---------------------
--   | || | | | '_ \ / _ \ | |_) / _` | '__/ __|/ _ \ '__| ---------------------
--   | || |_| | |_) |  __/ |  __/ (_| | |  \__ \  __/ |    ---------------------
--   |_| \__, | .__/ \___| |_|   \__,_|_|  |___/\___|_|    ---------------------
--       |___/|_|                                          ---------------------

mutual
  typeP : Parser TypePos
  typeP = do
    p  <- getPosition
    tp <- typeNonNull
    mb <- opt $ char '?'
    pure $ case mb of
      Nothing => tp
      Just _  => Ann p $ TNull tp

  typeNonNull : Parser TypePos
  typeNonNull = typeParenOrFun <|>| commitTo typeParams

  typeParams : Parser TypePos
  typeParams = do
    p  <- getPosition
    tp <- ident
    mtps <- opt $ char '<' >! do
      tps <- sepBy1 typeP (char ',')
      skip $ char '>'
      pure $ tps
    pure $ Ann p $ TParam tp $ fromMaybe [] mtps

  typeParenOrFun : Parser TypePos
  typeParenOrFun = do
    p   <- getPosition
    tps <- parens (sepBy typeP (char ','))
    ret <- opt $ string "->" >>= \_ => commitTo typeP
    case ret of
      Nothing => case tps of
                   [tp] => pure tp
                   _    => fail "Invalid syntax"
      Just rt => pure $ Ann p $ TFun tps rt


--  ____                             ____                           ------------
-- |  _ \ __ _ _ __ __ _ _ __ ___   |  _ \ __ _ _ __ ___  ___ _ __  ------------
-- | |_) / _` | '__/ _` | '_ ` _ \  | |_) / _` | '__/ __|/ _ \ '__| ------------
-- |  __/ (_| | | | (_| | | | | | | |  __/ (_| | |  \__ \  __/ |    ------------
-- |_|   \__,_|_|  \__,_|_| |_| |_| |_|   \__,_|_|  |___/\___|_|    ------------
--                                                                  ------------

mutual
  paramP : Parser ParamPos
  paramP = do
    p  <- getPosition
    id <- ident
    skip $ string ":"
    tp <- typeP
    pure $ Ann p $ Param id tp



--  ____                            ____   ____                           ------
-- |  _ \ __ _ _ __ __ _ _ __ ___  / ___| |  _ \ __ _ _ __ ___  ___ _ __  ------
-- | |_) / _` | '__/ _` | '_ ` _ \| |     | |_) / _` | '__/ __|/ _ \ '__| ------
-- |  __/ (_| | | | (_| | | | | | | |___  |  __/ (_| | |  \__ \  __/ |    ------
-- |_|   \__,_|_|  \__,_|_| |_| |_|\____| |_|   \__,_|_|  |___/\___|_|    ------
--                                                                        ------

mutual
  paramCP : Parser ParamCPos
  paramCP = do
    p    <- getPosition
    qual <- string "var" <|>| string "val"
    id   <- ident
    skip $ string ":"
    tp   <- typeP
    pure $ Ann p $ if qual == "var" then PCVar id tp
                                    else PCVal id tp


