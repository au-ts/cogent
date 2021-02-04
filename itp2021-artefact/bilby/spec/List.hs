
module List where

butlast :: [a] -> [a]
butlast [] = []
butlast (x:xs) = if null xs then [] else x:butlast xs

fold :: (a -> b -> b) -> [a] -> b -> b
fold f [] = id
fold f (x:xs) = fold f xs . f x
