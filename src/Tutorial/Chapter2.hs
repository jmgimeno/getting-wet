module Tutorial.Chapter2 where

{-@ (==>) :: p:Bool -> q:Bool -> {v:Bool | v <=> (p ==> q)} @-}
False ==> False = True
False ==> True  = True
True  ==> True  = True
True  ==> False = False

{-@ (<=>) :: p:Bool -> q:Bool -> {v:Bool | v <=> (p <=> q)} @-}
False <=> False = True
False <=> True  = False
True  <=> True  = True
True  <=> False = False

{-@ type TRUE  = {v: Bool | v     } @-}
{-@ type FALSE = {v: Bool | not v } @-}

{-@ ex0 :: TRUE @-}
ex0 = True

{-@ ex0' :: FALSE @-}
ex0' = False

{-@ ex1 :: Bool -> TRUE @-}
ex1 b = b || not b

{-@ ex2 :: Bool -> FALSE @-}
ex2 b = b && not b

{-@ ex3 :: Bool -> Bool -> TRUE @-}
ex3 a b = (a && b) ==> a

{-@ ex4 :: Bool -> Bool -> TRUE @-}
ex4 a b = (a && b) ==> b

-- Exercise 2.1

{-@ ex3' :: Bool -> Bool -> TRUE @-}
ex3' a b = a ==> (a || b)

{-@ ex4' :: Bool -> Bool -> TRUE @-}
ex4' a b = b ==> (a || b)

--

{-@ ex6 :: Bool -> Bool -> TRUE @-}
ex6 a b = (a && (a ==> b)) ==> b

{-@ ex7 :: Bool -> Bool -> TRUE @-}
-- ex7 a b = a ==> (a ==> b) ==> b    -- This should work according to the tutorial but
-- ex7 a b = (a ==> (a ==> b)) ==> b  -- Also fails
ex7 a b = a ==> ((a ==> b) ==> b)    

{-@ exDemorgan1 :: Bool -> Bool -> TRUE @-}
exDemorgan1 a b = not (a || b) <=> (not a && not b)

-- Exercise 2.2

{-@ exDemorgan2 :: Bool -> Bool -> TRUE @-}
exDemorgan2 a b = not (a && b) <=> (not a || not b)

--

