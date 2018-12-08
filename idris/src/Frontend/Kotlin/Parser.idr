
module Frontend.Kotlin.Parser

import Frontend.Kotlin.AST
import Frontend.Kotlin.PrettyPrinter
import Tools.Annotation
import Lightyear.Core
import Lightyear.Char
import Lightyear.Strings
import Lightyear.Combinators
import Lightyear.Position

%access public export

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

(>>) : Monad m => m a -> m b -> m b
m >> m' = m >>= \_ => m'

infixl 10 <**>
(<**>) : Parser a -> Parser b -> Parser (Either a b)
pa <**> pb = Left  <$> pa
        <|>| Right <$> pb

unmaybe : Maybe (List a) -> List a
unmaybe Nothing  = []
unmaybe (Just l) = l


--  ____              _              -------------------------------------------
-- / ___| _   _ _ __ | |_ __ ___  __ -------------------------------------------
-- \___ \| | | | '_ \| __/ _` \ \/ / -------------------------------------------
--  ___) | |_| | | | | || (_| |>  <  -------------------------------------------
-- |____/ \__, |_| |_|\__\__,_/_/\_\ -------------------------------------------
--        |___/                      -------------------------------------------

ident : Parser String
ident = do
  h <- letter <|> char '_'
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
                 <|>| (commentStar >> commentStarString)
                 <|>| (anyChar >> commentStarString)
  
  commentStar : Parser ()
  commentStar = string "/*" >! commentStarString

mutual
  commentLineString : Parser ()
  commentLineString = (skip $ endOfLine)
                 <|>| (anyChar >> commentLineString)

  commentLine : Parser ()
  commentLine = string "//" >! commentLineString


comment : Parser ()
comment = commentStar <|>| commentLine

white : Parser ()
white = skip $ many $ (skip $ oneOf " \t\n") <|>| comment

white1 : Parser ()
white1 = skip $ some $ (skip $ oneOf " \t\n") <|>| comment

wstring : String -> Parser ()
wstring str = white >> string str >> white


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
    mb <- opt $ white >> char '?'
    pure $ case mb of
      Nothing => tp
      Just _  => Ann p $ TNull tp

  typeNonNull : Parser TypePos
  typeNonNull = typeParenOrFun <|>| commitTo typeParams

  typeParams : Parser TypePos
  typeParams = do
    p  <- getPosition
    tp <- ident
    mtps <- opt $ white >> char '<' >! do
      tps <- sepBy1 typeP $ wstring ","
      skip $ white >> char '>'
      pure $ tps
    pure $ Ann p $ TParam tp $ fromMaybe [] mtps

  typeParenOrFun : Parser TypePos
  typeParenOrFun = do
    p   <- getPosition
    tps <- parens (sepBy typeP $ wstring ",")
    ret <- opt $ wstring "->" >> commitTo typeP
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
    white
    skip $ string ":"
    white
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
    white1
    id   <- ident
    wstring ":"
    tp   <- typeP
    pure $ Ann p $ if qual == "var" then PCVar id tp
                                    else PCVal id tp


--  _____                   ____                           ---------------------
-- | ____|_  ___ __  _ __  |  _ \ __ _ _ __ ___  ___ _ __  ---------------------
-- |  _| \ \/ / '_ \| '__| | |_) / _` | '__/ __|/ _ \ '__| ---------------------
-- | |___ >  <| |_) | |    |  __/ (_| | |  \__ \  __/ |    ---------------------
-- |_____/_/\_\ .__/|_|    |_|   \__,_|_|  |___/\___|_|    ---------------------
--            |_|                                          ---------------------

mutual
  exprP : Parser ExprPos
  exprP = exprP10

  exprP10 : Parser ExprPos
  exprP10 = exprIf <|>| exprP9

  exprIf : Parser ExprPos
  exprIf = getPosition >>= \p => keyword IF >! do
    wstring "("
    cond <- exprP
    wstring ")"
    body <- blockExprP
    els  <- opt $ do
      white
      keyword ELSE
      white
      blockExprP
    pure $ Ann p $ EIfElse cond body els

  exprP9 : Parser ExprPos
  exprP9 = exprReturn <|>| exprWhile <|>| exprP8

  exprReturn : Parser ExprPos
  exprReturn = keyword RETURN >! white1 >> exprP

  exprWhile : Parser ExprPos
  exprWhile = getPosition >>= \p => keyword WHILE >! do
    wstring "("
    cond <- exprP
    wstring ")"
    body <- blockExprP
    pure $ Ann p $ EWhile cond body

  exprP8 : Parser ExprPos
  exprP8 = do
    p  <- getPosition
    e1 <- exprP7
    white
    e2 <- opt $ parseEq p e1
    pure $ case e2 of
      Nothing => e1
      Just e' => e'
   where parseEq : Position -> ExprPos -> Parser ExprPos
         parseEq p e1 = do
           skip $ string "="
           white
           er <- exprP
           case e1 of
             Ann _ (EAccess access) => pure $ Ann p $ EAss access er
             _                      => fail "Expected access"

  exprP7 : Parser ExprPos
  exprP7 = do
    p  <- getPosition
    e1 <- exprP6
    white
    e2 <- opt $ binopP p e1 Or exprP7
    pure $ case e2 of
      Nothing => e1
      Just e' => e'

  exprP6 : Parser ExprPos
  exprP6 = do
    p  <- getPosition
    e1 <- exprP5
    white
    e2 <- opt $ binopP p e1 And exprP6
    pure $ case e2 of
      Nothing => e1
      Just e' => e'

  exprP5 : Parser ExprPos
  exprP5 = do
    p  <- getPosition
    e1 <- exprP4
    white
    e2 <- opt $ ( binopP p e1 RefEq     exprP5
             <|>| binopP p e1 RefNeq    exprP5
             <|>| binopP p e1 StructEq  exprP5
             <|>| binopP p e1 StructNeq exprP5)
    pure $ case e2 of
      Nothing => e1
      Just e' => e'

  exprP4 : Parser ExprPos
  exprP4 = do
    p  <- getPosition
    e1 <- exprP3
    white
    e2 <- opt $ ( binopP p e1 Lt exprP4
             <|>| binopP p e1 Le exprP4
             <|>| binopP p e1 Gt exprP4
             <|>| binopP p e1 Ge exprP4)
    pure $ case e2 of
      Nothing => e1
      Just e' => e'

  exprP3 : Parser ExprPos
  exprP3 = do
    p  <- getPosition
    e1 <- exprP2
    white
    e2 <- opt $ ( binopP p e1 Plus exprP3
             <|>| binopP p e1 Subs exprP3)
    pure $ case e2 of
      Nothing => e1
      Just e' => e'

  exprP2 : Parser ExprPos
  exprP2 = do
    p  <- getPosition
    e1 <- exprP1
    white
    e2 <- opt $ ( binopP p e1 Mult   exprP2
             <|>| binopP p e1 Div    exprP2
             <|>| binopP p e1 Modulo exprP2)
    pure $ case e2 of
      Nothing => e1
      Just e' => e'

  binopP : Position -> ExprPos -> Operator -> Parser ExprPos -> Parser ExprPos
  binopP p al op p2 = (string $ show op) >! do
    white
    ar <- p2
    pure $ Ann p $ EOp op al ar

  exprP1 : Parser ExprPos
  exprP1 = getPosition >>= \p => ( string "-" >! white >> (Ann p <$> (EMinus <$> exprP1))
                              <|>| string "!" >! white >> (Ann p <$> (ENot   <$> exprP1))
                              <|>| exprP0 )

  exprP0 : Parser ExprPos
  exprP0 = do
    p     <- getPosition
    start <- exprP0'
    subs  <- many subP
    pure $ foldl (\ep => \(sym,p',sub) => Ann p $ EAccess $ Ann p'
                                        $ if sym == "?." then ANSub ep sub else ASub ep sub)
                 start subs
   where subP : Parser (String, Position, Ident)
         subP = do
           white
           str <- string "?." <|>| string "."
           white
           p   <- getPosition
           sub <- ident
           pure $(str, p, sub)

  exprP0' : Parser ExprPos
  exprP0' = getPosition >>= \p => ( keyword TRUE  >> pure (Ann p ETrue)
                               <|>| keyword FALSE >> pure (Ann p EFalse)
                               <|>| keyword THIS  >> pure (Ann p EThis)
                               <|>| keyword NULL  >> pure (Ann p ENull)
                               <|>| Ann p <$> (EInt <$> number)
                               <|>| Ann p <$> (EStr <$> string)
                               <|>| keyword FUN >! efunP p
                               <|>| string "(" >> white >>
                                      (exprP >>= \p => white >> string ")" >> pure p)
                               <|>| callP
                               <|>| Ann p <$> (EAccess <$> (Ann p <$> (AIdent <$> ident))))

  efunP : Position -> Parser ExprPos
  efunP p = do
    wstring "("
    args <- sepBy paramP $ wstring ","
    wstring ")"
    tp   <- opt $ string ":" >! white >> typeP
    white
    body <- blockP
    pure $ Ann p $ EFun args tp body

  callP : Parser ExprPos
  callP = getPosition >>= \p =>
          ident >>= \id =>
          wstring "(" >>= \_ => commitTo $ do
    args <- sepBy exprP $ wstring ","
    white
    string ")"
    pure $ Ann p $ ECall id args

  blockP : Parser BlockPos
  blockP = string "{" >>= \_ => commitTo $ do
    white
    body <- sepBy (varP <**> exprP) $ wstring ";"
    if length body > 0 then opt $ white >> string ";" else pure Nothing
    white
    p <- getPosition
    skip $ string "}"
    pure $ foldr storer (Ann p BEmpty) body
   where storer : Either VarPos ExprPos
               -> BlockPos -> BlockPos
         storer (Left  (Ann p var))  acc = Ann p $ BVar  (Ann p var)  acc
         storer (Right (Ann p expr)) acc = Ann p $ BExpr (Ann p expr) acc

  blockExprP : Parser BlockExprPos
  blockExprP = Ann <$> getPosition <*> ( BEBlock <$> blockP
                                    <|>| BEExpr  <$> commitTo exprP)

  varP : Parser VarPos
  varP = do
    p    <- getPosition
    qual <- string "var" <|>| string "val"
    white1
    id   <- ident
    tp   <- opt $ wstring ":" >! typeP
    wstring "="
    expr <- exprP
    pure $ Ann p $ if qual == "var" then VVar id tp expr
                                    else VVal id tp expr



--   ____ _                 ____                           ---------------------
--  / ___| | __ _ ___ ___  |  _ \ __ _ _ __ ___  ___ _ __  ---------------------
-- | |   | |/ _` / __/ __| | |_) / _` | '__/ __|/ _ \ '__| ---------------------
-- | |___| | (_| \__ \__ \ |  __/ (_| | |  \__ \  __/ |    ---------------------
--  \____|_|\__,_|___/___/ |_|   \__,_|_|  |___/\___|_|    ---------------------
--                                                         ---------------------

mutual
  classP : Parser ClassPos
  classP = do
    p <- getPosition
    keyword DATA
    white1
    keyword CLASS
    white1
    name   <- ident
    params <- opt $ wstring "<" >! do
      prms <- sepBy1 ident $ wstring ","
      white
      skip $ string ">"
      pure prms
    wstring "("
    args   <- sepBy1 paramCP $ wstring ","
    wstring ")"
    body   <- opt $ wstring "{" >! do
      vars <- sepBy varP $ wstring ";"
      if length vars > 0 then opt $ wstring ";" else pure Nothing
      white
      skip $ string "}"
      pure vars
    pure $ Ann p $ Class name (unmaybe params) args (unmaybe body)



--  _____              ____                           --------------------------
-- |  ___|   _ _ __   |  _ \ __ _ _ __ ___  ___ _ __  --------------------------
-- | |_ | | | | '_ \  | |_) / _` | '__/ __|/ _ \ '__| --------------------------
-- |  _|| |_| | | | | |  __/ (_| | |  \__ \  __/ |    --------------------------
-- |_|   \__,_|_| |_| |_|   \__,_|_|  |___/\___|_|    --------------------------
--                                                    --------------------------

mutual
  funP : Parser FunPos
  funP = do
    p <- getPosition
    keyword FUN
    params <- opt $ wstring "<" >! do
      prms <- sepBy1 ident $ wstring ","
      white
      skip $ string ">"
      pure prms
    white
    name   <- ident
    wstring "("
    args   <- sepBy paramP $ wstring ","
    white
    skip $ string ")"
    tp     <- opt $ wstring ":" >! typeP
    white
    body   <- blockP
    pure $ Ann p $ Fun (unmaybe params) name args tp body


--  ____            _   ____                           -------------------------
-- |  _ \  ___  ___| | |  _ \ __ _ _ __ ___  ___ _ __  -------------------------
-- | | | |/ _ \/ __| | | |_) / _` | '__/ __|/ _ \ '__| -------------------------
-- | |_| |  __/ (__| | |  __/ (_| | |  \__ \  __/ |    -------------------------
-- |____/ \___|\___|_| |_|   \__,_|_|  |___/\___|_|    -------------------------
--                                                     -------------------------

mutual
  declP : Parser DeclPos
  declP = getPosition >>= \p => Ann p <$> declP'

  declP' : Parser (SyntaxF (\id => SyntaxAnn id Position) DeclTy)
  declP' = DFun   <$> funP
      <|>| DClass <$> classP
      <|>| DVar   <$> (varP >>= \v => white >> string ";" >> pure v)


--  _____ _ _        ____                           ----------------------------
-- |  ___(_) | ___  |  _ \ __ _ _ __ ___  ___ _ __  ----------------------------
-- | |_  | | |/ _ \ | |_) / _` | '__/ __|/ _ \ '__| ----------------------------
-- |  _| | | |  __/ |  __/ (_| | |  \__ \  __/ |    ----------------------------
-- |_|   |_|_|\___| |_|   \__,_|_|  |___/\___|_|    ----------------------------
--                                                  ----------------------------

mutual
  fileP : Parser FilePos
  fileP = do
    p     <- getPosition
    white
    decls <- sepBy declP white
    white
    eof
    pure $ Ann p $ File decls


