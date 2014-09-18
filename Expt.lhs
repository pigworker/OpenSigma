> {-# LANGUAGE GeneralizedNewtypeDeriving #-}

> module Expt where

> import Control.Applicative
> import Control.Monad
> import Data.Monoid
> import Data.Traversable
> import Control.Arrow ((***))
> import Data.List
> import Data.Char

> data Block = String :/ [Block] deriving Show

> dentBlocks :: Int -> [(Int, String)] -> ([Block], [(Int, String)])
> dentBlocks i ((j, s) : jss) | j > i = ((s :/ ts) : bs, lss) where
>   (ts, kss) = dentBlocks j jss
>   (bs, lss) = dentBlocks i kss
> dentBlocks _ jss = ([], jss)

> layout :: Block -> Block
> layout b@(s :/ bs) = case span isSpace (reverse s) of -- optimise later
>   (_, ':':'-':_) -> s :/ map layout bs
>   _ -> case bs of
>     (c :/ cs) : bs -> layout ((s ++ " " ++ c) :/ (cs ++ bs))
>     _ -> b

> blockify :: String -> [Block]
> blockify =
>   map layout .
>   fst . dentBlocks (negate 1) .
>   map ((length *** id) . span isSpace) . lines


> newtype Parser x = Parser {parse :: String -> [(x, String)]}
>   deriving Monoid

> ch :: (Char -> Bool) -> Parser Char
> ch p = Parser $ \ s -> case s of
>   c : s | p c -> [(c, s)]
>   _ -> []

> kw :: String -> Parser ()
> kw x = () <$ traverse (ch . (==)) x

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
