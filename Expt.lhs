> {-# LANGUAGE GeneralizedNewtypeDeriving, GADTs #-}

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
>   | RawType :/ RawType
>   | RawRange (Maybe RawTerm) (Maybe RawTerm)
>   | RawEnum [String]
>   deriving (Show, Eq)

> data RawTerm
>   = RawTmId String
>   | RawIntLit Int
>   deriving (Show, Eq)

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
>   (t :/) <$ pu "," <*> pRawType <|> pure t

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
