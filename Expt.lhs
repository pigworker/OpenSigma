> {-# LANGUAGE GeneralizedNewtypeDeriving, GADTs, RankNTypes #-}

> module Expt where

> import Control.Applicative
> import Control.Monad
> import Data.Monoid
> import Data.Foldable (fold)
> import Data.Traversable
> import Control.Arrow ((***))
> import Data.List
> import Data.Char
> import Data.Void
> import Data.Either

> data Block = String :-: [Block] deriving Show

> dentBlocks :: Int -> [(Int, String)] -> ([Block], [(Int, String)])
> dentBlocks i ((_, "") : jss) = dentBlocks i jss
> dentBlocks i ((j, s) : jss) | j > i = ((s :-: ts) : bs, lss) where
>   (ts, kss) = dentBlocks j jss
>   (bs, lss) = dentBlocks i kss
> dentBlocks _ jss = ([], jss)

> layout :: Block -> Block
> layout b@(s :-: bs) = case span isSpace (reverse s) of -- optimise later
>   (_, ':':'-':s) -> reverse s :-: map layout bs
>   _ -> case bs of
>     (c :-: cs) : bs -> layout ((s ++ " " ++ c) :-: (cs ++ bs))
>     _ -> b

> blockify :: String -> [Block]
> blockify =
>   map layout .
>   fst . dentBlocks (negate 1) .
>   map ((length *** id) . span isSpace) . lines

> data BlockParser t where
>   BP :: Parser a -> (a -> SubParser t) -> BlockParser t

> data SubParser t where
>   SP :: BlockParser b -> ([b] -> t) -> SubParser t

> blockParse :: BlockParser t -> Block -> [t]
> blockParse (BP ap sp) (h :-: ss) = do
>   a <- parseAll ap h
>   case (sp a) of
>     SP b k -> do
>       k <$> traverse (blockParse b) ss

> instance Monoid (BlockParser t) where
>   mempty = BP mempty absurd
>   mappend (BP a j) (BP b k) =
>     BP (Left <$> a <|> Right <$> b) (either j k)

> data Decl
>   = Class String [Decl]
>   | Prop String [Decl]
>   | For RawType [Decl]
>   | Unique String RawType
>   | Field String RawType
>   deriving (Show, Eq)

> data RawType
>   = RawTyString
>   | RawTyId String
>   | RawType :/: RawType
>   | RawRange (Maybe RawTerm) (Maybe RawTerm)
>   | RawEnum [String]
>   deriving (Show, Eq)

> data RawTerm
>   = RawTmId String
>   | RawIntLit Int
>   deriving (Show, Eq)

> data Ty
>   = UN
>   | Ty :/ Ty
>   | C String Tm
>   | P String Tm
>   | INT | STRING
>   | ENUM [String]
>   deriving Show

> data Tm
>   = Tm :& Tm
>   | EV [Int]
>   | IND Int
>   | ILIT Int
>   | SLIT String
>   deriving (Show, Eq)

> data TCS o where
>   QClass :: String -> TCS Ty
>   QProp  :: String -> TCS Ty
>   QField :: String -> TCS Ty
>   Error  :: String -> TCS Void

> data SM s x where
>   Ret :: x -> SM s x
>   (:?) :: s y -> (y -> SM s x) -> SM s x

> (??) :: (i -> s o) -> i -> SM s o
> c ?? i = c i :? Ret

> instance Monad (SM s) where
>   return = Ret
>   Ret x >>= k = k x
>   (c :? j) >>= k = c :? ((>>= k) . j)
> instance Applicative (SM s) where
>   pure = return
>   (<*>) = ap
> instance Functor (SM s) where
>   fmap = ap . return 

> algHandle :: (x -> t) -> (forall o. s o -> (o -> t) -> t) -> SM s x -> t
> algHandle ret hand (Ret x) = ret x
> algHandle ret hand (c :? k) = hand c (algHandle ret hand . k)

> works :: SM TCS x -> SM TCS Bool
> works = algHandle (const (Ret True)) $ \ c k -> case c of
>   Error _ -> Ret False
>   _ -> c :? k

> data Bwd x = B0 | Bwd x :< x deriving Show
> data Entry
>   = CI String Tm (Maybe Int)
>   | PP String Tm
>   | FV Ty (Maybe Tm)
>   deriving Show
> type Cx = (Bwd (Int, Entry), Int)

> (!<) :: Cx -> Entry -> Cx
> (ez, i) !< e = (ez :< (i, e), i + 1)

> (!<:) :: Cx -> Ty -> Cx
> (ez, i) !<: t = (ez :< (i, FV t Nothing), i + 1)

> proj :: Cx -> Int -> SM TCS Ty
> proj (g, _) i = go g where
>   go (g :< (j, e))
>     | i == j = case e of
>       CI c u _ -> return (C c u)
>       PP p u -> return (P p u)
>       FV t _ -> return t
>     | otherwise = go g
>   go _ = Error "scope" :? absurd

> kerCxTy :: Cx -> Ty -> SM TCS Cx
> kerCxTy g UN = return g
> kerCxTy g INT = return (g !<: INT)
> kerCxTy g STRING = return (g !<: STRING)
> kerCxTy g (ENUM ts) =
>   if length (nub ts) == length ts then return (g !<: ENUM ts)
>     else Error ("Duplicates in enumeration " ++ show ts) :? absurd
> kerCxTy g (i :/ j) = do
>   g' <- kerCxTy g i
>   kerCxTy g' j
> kerCxTy g (C c v) = do
>   j <- QClass ?? c
>   kerCxTm g j v
>   return (g !< CI c v Nothing)
> kerCxTy g (P p v) = do
>   j <- QProp ?? p
>   kerCxTm g j v
>   return (g !< PP p v)

> kerCxTm :: Cx -> Ty -> Tm -> SM TCS Cx
> kerCxTm g (i :/ j) (u :& v) = do
>   g' <- kerCxTm g i u
>   kerCxTm g' j v
> kerCxTm g INT (ILIT i) = return (g !< FV INT (Just (ILIT i)))
> kerCxTm g STRING (SLIT s) = return (g !< FV STRING (Just (SLIT s)))
> kerCxTm g t@(ENUM ts) (SLIT s)
>   | elem s ts = return (g !< FV t (Just (SLIT s)))
>   | otherwise = Error (s ++ " </: " ++ show ts) :? absurd
> kerCxTm g UN _ = return g
> kerCxTm g (P p v) (EV xs) = do
>   ps <- traverse (proj g) xs
>   j <- QProp ?? p
>   prove g ps (p, v)
>   return (g !< PP p v)
> kerCxTm g t@(C c v) (IND x) = do
>   j <- QClass ?? c
>   i <- proj g x
>   case i of
>     C c' u | c == c' -> kerEqIn g j (u, v) >> return g
>     _ -> Error (show g ++ " . " ++ show x ++ " </: " ++ show t) :? absurd
> kerCxTm g i u = Error (show i ++ " :/> " ++ show u) :? absurd

> kerEqIn :: Cx -> Ty -> (Tm, Tm) -> SM TCS ()
> kerEqIn _ (P _ _) _ = return ()
> kerEqIn g t (IND x, IND y)
>   | canon g x == canon g y = return ()
>   | otherwise = Error (show x ++ " is not " ++ show y ++ " in " ++ show t) :? absurd
> kerEqIn _ t (a, b)
>   | a == b = return ()
>   | otherwise = Error ("Mismatch: " ++ show t ++ " :> " ++ show a ++ " != " ++ show b) :? absurd

> canon :: Cx -> Int -> Int
> canon (g, _) x = go x g where
>   go x B0 = x
>   go x (g :< (y, CI _ _ d)) | x == y = case d of
>     Nothing -> x
>     Just z -> go z g
>   go x (g :< _) = go x g

> prove :: Cx -> [Ty] -> (String, Tm) -> SM TCS ()
> prove g ps (p, v) = do
>   j <- QProp ?? p
>   let go [] = Error ("No proof for " ++ p ++ " " ++ show v) :? absurd
>       go (P q u : ps) | p == q = do
>         b <- works (kerEqIn g j (u, v))
>         if b then return () else go ps
>       go (_ : ps) = go ps
>   go ps

> bDecl :: BlockParser Decl
> bDecl = fold
>   [ BP (id <$ kw "class" <*> pId) (\ s -> SP bDecl (Class s))
>   , BP (id <$ kw "prop" <*> pId) (\ s -> SP bDecl (Prop s))
>   , BP (id <$ kw "for" <*> pRawType) (\ t -> SP bDecl (For t))
>   , BP (Unique <$> pId <* pu "!" <*> pRawType) (\ d -> SP mempty (const d))
>   , BP (Field <$> pId <* pu ":" <*> pRawType) (\ d -> SP mempty (const d))
>   ]

> pRawType :: Parser RawType
> pRawType = pWeeRawType >>= \ t ->
>   (t :/:) <$ pu "," <*> pRawType <|> pure t

> keywords :: [String]
> keywords = ["class", "prop", "for", "String", "Int"]

> pId :: Parser String
> pId = do
>   x <- ((:) <$ spc <*> ch isAlpha <*> many (ch isAlphaNum) <* etok <* spc)
>   guard (not (elem x keywords))
>   return x

> pWeeRawType :: Parser RawType
> pWeeRawType
>   =    RawTyString <$ kw "String"
>   <|>  RawRange Nothing Nothing <$ kw "Int"
>   <|>  RawTyId <$> pId
>   <|>  RawRange <$ pu "[" <*>
>          pOpt pRawTerm <* pu ".." <*> pOpt pRawTerm <* pu "]"
>   <|>  RawEnum <$ pu "{" <*> pSep (pu ",") pId <* pu "}"
>   <|>  id <$ pu "(" <*> pRawType <* pu ")"

> pSep :: Parser () -> Parser a -> Parser [a]
> pSep s a = (:) <$> a <*> many (id <$ s <*> a) <|> pure []

> pOpt :: Parser a -> Parser (Maybe a)
> pOpt p = Just <$> p <|> pure Nothing

> pInt :: Parser Int
> pInt = read <$ spc <*> (((:) <$> ch (== '-') <|> pure id)
>   <*> some (ch isDigit) <* spc)

> pRawTerm :: Parser RawTerm
> pRawTerm
>   =    RawIntLit <$> pInt
>   <|>  RawTmId <$> pId

> newtype Parser x = Parser {parse :: String -> [(x, String)]}
>   deriving Monoid

> parseAll :: Parser a -> String -> [a]
> parseAll p s = do
>   (a, s) <- parse p s
>   guard (all isSpace s)
>   return a

> ch :: (Char -> Bool) -> Parser Char
> ch p = Parser $ \ s -> case s of
>   c : s | p c -> [(c, s)]
>   _ -> []

> spc :: Parser ()
> spc = Parser $ \ s -> let (_, s') = span isSpace s in [((), s')]

> kw :: String -> Parser ()
> kw x = () <$ spc <* traverse (ch . (==)) x <* etok <* spc

> pu :: String -> Parser ()
> pu x = () <$ spc <* traverse (ch . (==)) x <* spc

> etok :: Parser ()
> etok = Parser $ \ s -> case s of
>   c : _ | isAlphaNum c -> []
>   _ -> [((), s)]

> etxt :: Parser ()
> etxt = Parser $ \ s -> do
>   guard (all isSpace s)
>   [((), "")]

> instance Monad Parser where
>   return x = Parser $ \ s -> [(x, s)]
>   Parser p >>= k = Parser $ \ s -> do
>     (x, s) <- p s
>     parse (k x) s

> instance Applicative Parser where
>   pure = return
>   (<*>) = ap

> instance Functor Parser where
>   fmap = ap . return

> instance Alternative Parser where
>   empty = mempty
>   (<|>) = mappend

> instance MonadPlus Parser where
>   mzero = mempty
>   mplus = mappend
