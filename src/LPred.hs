module LPred where

import Data.List
--import Data.String

data Term = Var String | Func String [Term] deriving (Eq, Show)

type Simbolo = String

data Formula = Top | Bottom 
             | Predicado Simbolo [Term]
             | Not Formula
             | And Formula Formula  | Or Formula Formula
             | Impl Formula Formula | Iff Formula Formula
             | ForAll Simbolo Formula | Exists Simbolo Formula
             deriving (Eq, Show)

type Sustitucion = (String,Term)

infixr 4 `ForAll`, `Exists`
infixl 3 `And`, `Or`
infixl 2 `Iff`
infixl 1 `Impl`

libres :: Formula -> [String]
libres Top = []
libres Bottom = []
libres (Predicado _ ts) = nub ( concatMap varsTermin ts )
libres (Not p) = nub (libres p)
libres (And p q) = nub (libres p ++ libres q)
libres (Or p q) = nub (libres p ++ libres q)
libres (Iff p q) = nub (libres p ++ libres q)
libres (Impl p q) = nub (libres p ++ libres q)
libres (ForAll a b) = filter(/=a) (libres b)
libres (Exists a b) = filter(/=a) (libres b)

varsTermin :: Term -> [String]
varsTermin (Var v) = [v]
varsTermin (Func _ t) = nub (concatMap varsTermin t)

ligadas :: Formula -> [String]
ligadas Top = []
ligadas Bottom = []
ligadas (Predicado a ts) = nub( ligados (Predicado a ts) [])
ligadas (Not p) = ligadas p
ligadas (And p q) = nub(ligadas p ++ ligadas q)
ligadas (Or p q) = nub(ligadas p ++ ligadas q)
ligadas (Iff p q) = nub(ligadas p ++ ligadas q)
ligadas (Impl p q) = nub (ligadas p ++ ligadas q)
ligadas (ForAll a b) = ligados b a
ligadas (Exists a b) = ligados b a

ligados :: Formula -> String -> [String]
ligados Top _ = []
ligados Bottom _ = []
ligados (Predicado a ts) s = filter(==s) (nub( concatMap varsTermin ts ))
ligados (Not p) s = ligados p s
ligados (And p q) s = nub((ligados p s) ++ (ligados q s))
ligados (Or p q) s = nub((ligados p s) ++ (ligados q s))
ligados (Iff p q) s = nub((ligados p s) ++ (ligados q s))
ligados (Impl p q) s = nub((ligados p s)++(ligados q s))
ligados (ForAll a b) s = nub((ligados b s) ++ (ligados b a))
ligados (Exists a b) s = nub((ligados b s) ++ (ligados b a))

sustv1 :: Formula -> Sustitucion -> Formula
sustv1 Top (s,p) = Top
sustv1 Bottom (s,p) = Bottom
sustv1 (Predicado a (t:ts)) (s,p) = Predicado a (sustList (t:ts) (s,p))
sustv1 (Not a) (s,p) = Not (sustv1 a (s,p))
sustv1 (And a b) (s,p) = And (sustv1 a (s,p)) (sustv1 b (s,p))
sustv1 (Or a b) (s,p) = Or (sustv1 a (s,p)) (sustv1 b (s,p))
sustv1 (Iff a b) (s,p) = Iff (sustv1 a (s,p)) (sustv1 b (s,p))
sustv1 (Impl a b) (s,p) = Impl (sustv1 a (s,p)) (sustv1 b (s,p))
sustv1 (ForAll a b) (s,p) = if (elem a [s]) == True then (ForAll a b) else (ForAll a (sustv1 b (s,p)))
sustv1 (Exists a b) (s,p) = if (elem a [s]) == True then (Exists a b) else (Exists a (sustv1 b (s,p)))

--Funcion auxiliar que sustituye los datos tipo Term de una lista
sustList :: [Term] -> Sustitucion -> [Term]
sustList [] (s,p) = []
sustList (t:ts) (s,p) = (sustVar t (s,p)) : (sustList ts (s,p))

--Funcion auxiliar que sustituye un dato tipo Term
sustVar :: Term -> Sustitucion -> Term
sustVar (Var q) (s,p) = if q == s then p else (Var q)
sustVar (Func a b) (s,p) = Func a (sustList b (s,p))

variables :: Formula -> [String]
variables Top = []
variables Bottom = []
variables (Predicado _ ts) = (concatMap varsTerminRepe ts )
variables (Not p) = variables p
variables (And p q) = variables p ++ variables q
variables (Or p q) = variables p ++ variables q
variables (Iff p q) = variables p ++ variables q
variables (Impl p q) = variables p ++ variables q
variables (ForAll a b) = [a] ++ variables b
variables (Exists a b) = [a] ++ variables b

varsTerminRepe :: Term -> [String]
varsTerminRepe (Var v) = [v]
varsTerminRepe (Func _ t) = concatMap varsTerminRepe t


sustGrosera :: Formula -> Sustitucion -> Formula
sustGrosera Top (s,p) = Top
sustGrosera Bottom (s,p) = Bottom
sustGrosera (Predicado a (t:ts)) (s,p) = Predicado a (sustList (t:ts) (s,p))
sustGrosera (Not a) (s,p) = Not (sustGrosera a (s,p))
sustGrosera (And a b) (s,p) = (sustGrosera a (s,p)) `And` (sustGrosera b (s,p))
sustGrosera (Or a b) (s,p) = (sustGrosera a (s,p)) `Or` (sustGrosera b (s,p))
sustGrosera (Iff a b) (s,p) = (sustGrosera a (s,p)) `Iff` (sustGrosera b (s,p))
sustGrosera (Impl a b) (s,p) = (sustGrosera a (s,p)) `Impl` (sustGrosera b (s,p))
sustGrosera (ForAll a b) (s,(Var p))
  | ( a == s ) = ForAll a (sustGrosera b (s,(Var p)))
  | otherwise = ForAll p (sustGrosera b (s,(Var p)))
sustGrosera (Exists a b) (s,(Var p))
  | ( a == s ) = Exists a (sustGrosera b (s,(Var p)))
  | otherwise = Exists p (sustGrosera b (s,(Var p)))
--sustGrosera (ForAll a b) (s,p) = if ( a == s ) then (ForAll a b) else (ForAll s (sustGrosera b (s,p)))
--sustGrosera (Exists a b) (s,p) = if ( a == s ) then (Exists a b) else (Exists s (sustGrosera b (s,p)))

sustitucionesGroseras :: Formula -> [Sustitucion] -> Formula
sustitucionesGroseras f [] = f
sustitucionesGroseras f [x] = sustGrosera f x
sustitucionesGroseras f (x:xs) = sustitucionesGroseras (sustGrosera f x) xs

crearSustitutos :: [String] -> [String] -> [Sustitucion]
crearSustitutos [] [] = []
crearSustitutos [a] [b]
  | a==b = []
  | otherwise = [(b,Var a)]
crearSustitutos (a:as) (b:bs) = crearSustitutos as bs `union` crearSustitutos [a] [b]


--"Se dicen que son alpha-equivalentes syss difieren a los mas en los nombres de las variables ligadas"
sonAlfaEquiv :: Formula -> Formula -> Bool
sonAlfaEquiv f1 f2
  | length (ligadas f1) /= length (ligadas f2) = False
  | otherwise = f1 == sustitucionesGroseras f2 (crearSustitutos (variables f1) (variables f2))



{-Idea inicial
sonAlfaEquiv (Not a) (Not b) = length(ligadas (Not a)) == lenth(ligadas (Not b))
sonAlfaEquiv (And a b) (And c d) = length(ligadas (And a b)) == length(ligadas (And c d))
sonAlfaEquiv (Or a b) (Or c d) = length(ligadas (Or a b)) == length(ligadas (Or c d))
sonAlfaEquiv (Iff a b) (Iff c d) = length(ligadas (Iff a b)) == length(ligadas (Iff c d))
sonAlfaEquiv (Impl a b) (Impl c d) = length(ligadas (Impl a b)) == length(ligadas (Impl c d))
sonAlfaEquiv (ForAll a b) (ForAll c d) = length(ligadas (ForAll a b)) == length(ligadas (ForAll c d))
sonAlfaEquiv (Exists a b) (Exists c d) = length(ligadas (Exists a b)) == length(ligadas (Exists c d))-}

--Funcion auxiliar para sonAlfaEquiv
--referencia https://cs.stackexchange.com/questions/76616/algorithm-for-deciding-alpha-equivalence-of-terms-in-languages-with-bindings
{--termIgual :: [(Term,Term)] -> Term -> Term -> Bool
termIgual [] x y = (x == y)
termIgual ((x,y):ts) u v = (x == u && y == v) || (x /= u && y /= v && termIgual ts u v)

listIgual :: [(Term,Term)] -> [Term] -> [Term] -> Bool
listIgual [] x y = False
listIgual ((x,y):ts) (u:us) (v:vs) = ((termIgual ((x,y):ts) u v) && (listIgual ts us vs))
      --(x /= v && y /= v && termIgual ts u v)

igual :: [(Term,Term)] -> Formula -> Formula -> Bool
igual _ _ _ = False
igual ts Top Top = True
igual ts Bottom Bottom = True
igual ts (Predicado a xa) (Predicado b xb) = (listIgual ts xa xb)
igual ts (Not a) (Not b) = (igual ts a b)
igual ts (And a b) (And c d) = (igual ts a c && igual ts b d)
igual ts (Or a b) (Or c d) = (igual ts a c && igual ts b d)
igual ts (Iff a b) (Iff c d) = (igual ts a c && igual ts b d)
igual ts (Impl a b) (Impl c d) = (igual ts a c && igual ts b d)
igual ts (ForAll a b) (ForAll c d) = (igual ((toString a, toString c):ts) b d)
  --(igual ((ligadas (ForAll a b), ligadas (ForAll a b)):ts) b d)
igual ts (Exists a b) (Exists c d) = (igual ((toString a, toString c):ts) b d)
  --(igual ((ligadas (Exists a b), ligadas (Exists a b)):ts) b d)

--igual :: [(Simbolo,Simbolo)] -> Formula -> Formula -> Bool-}


renombra :: Formula -> Formula
renombra (ForAll a b) = if a == "x" then sustv1 (ForAll a b) (a,Var "w")
                      else if a == "y" then sustv1 (ForAll a b) (a,Var "v") else (ForAll a b)
renombra (Exists a b) = if a == "x" then sustv1 (Exists a b) (a,Var "w")
                        else if a == "y" then sustv1 (Exists a b) (a,Var "v") else (Exists a b)
-- ~ sustituir ([ligadas], w)
-- funcion auxiliar que sustituya los simbolos/variasbles ligadas

sustv2 :: Formula -> Sustitucion -> Formula
sustv2 Top (s,p) = Top
sustv2 Bottom (s,p) = Bottom
sustv2 (Predicado a (t:ts)) (s,p) = Predicado a (sustList (t:ts) (s,p))
sustv2 (Not a) (s,p) = Not (sustv2 a (s,p))
sustv2 (And a b) (s,p) = And (sustv2 a (s,p)) (sustv1 b (s,p))
sustv2 (Or a b) (s,p) = Or (sustv2 a (s,p)) (sustv1 b (s,p))
sustv2 (Iff a b) (s,p) = Iff (sustv2 a (s,p)) (sustv1 b (s,p))
sustv2 (Impl a b) (s,p) = Impl (sustv2 a (s,p)) (sustv1 b (s,p))
sustv2 (ForAll a b) (s,p) = if (elem a [s]) == True then renombra (ForAll a b) else (ForAll a (sustv1 b (s,p)))
sustv2 (Exists a b) (s,p) = if (elem a [s]) == True then renombra (Exists a b) else (Exists a (sustv1 b (s,p)))

--unifica :: Formula -> Formula -> [Sustitucion]
--unifica (Predicado a x) (Predicado b y) = if (a == b) && (length x == length y) then inicio x y else error ("No es posible unificar " ++ a ++
                                                                            --   " con " ++ b)
--Aplica el algortimo de unificación en base a las listas de TERMS de los Predicados
--inicio :: [Term] -> [Term] -> [Sustitucion]
inicio :: [Term] -> [Term] -> [(Term,Term)]
inicio (x:xs) (y:ys) = (accQ (x:xs) (y:ys))

--Operacion 1
accU :: (Term,Term) -> (Term,Term)
accU (Func a [],Func b []) = if a == b then (Func "" [], Func "" []) else (Func a [],Func b [])

--Operaciones 2
accD :: (Term,Term) -> (Term,Term)
accD (Var x,Var y) = if x == y then (Var "",Var "") else (Var x, Var y)
--accUD ((Func a x),(Func b y)) = if a == b then inicio x y else error ("No es posible unificar " ++ a ++ " con " ++ b)
  --accTC inicio x y else error ("No es posible unificar " ++ a ++ " con " ++ b)
--accUD ((Func a x),(Var y)) = error ("No es posible unificar")

{--Operaciones 3 y 4 "Si X es una var del lado izquierdo, saca (y efectua) la sustitucion
Si X es una var del lado derecho, cambia de lado, saca (y efectua) la sustitucion-}
accT :: (Term,Term) -> Sustitucion
--accT (Func a x) (Func b y) =
accT (a,Var y) = (y,a)
--accTC (Var x,Func b y) = (x,(Func b y))
--accTC (Var x,Var y) = (x,(Var y))
--accT x (Var y) = (y,x)

--Operacion 4
accC :: (Term,Term) -> Sustitucion
accC (Var x,b) = (x,b)

--La problematica del tipo "f(x)=f(y)"
--accUD ((Func a x),(Func b y)) = if a == b then inicio x y else error ("No es posible unificar " ++ a ++ " con " ++ b)

accQ :: [Term] -> [Term] -> [(Term,Term)]
--Operacion 5, emparejo cada cabeza y hago las operaciones 1, 2, 3 y 4 (creo que aqui puede radicar el problema)
--accQ :: [Term] -> [Term] -> [Sustitucion]
accQ [] [] = []
accQ (x:xs) (y:ys) = (empareja x y) : (accQ xs ys)
  --(accTC(accUD (empareja x y)):(accQ xs ys))
--accQ ((Func a x),(Func b y)) = if a == b then inicio x y else error ("No es posible unificar " ++ a ++ " con " ++ b)

empareja :: Term -> Term -> (Term,Term)
--empareja _ _ = (_,_)
empareja x y = (x,y)
--empareja x _ = (x,_)
--empareja _ y = (_,y)

hayResolvente :: Formula -> Formula -> Bool
hayResolvente a _ = False

resolucion :: [Formula] -> [Formula] -> [Formula]
resolucion [a] _ = []