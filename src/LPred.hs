module LPred where

import Data.List

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

--"Se dicen que son alpha-equivalentes syss difieren a los mas en los nombres de las variables ligadas"
sonAlfaEquiv :: Formula -> Formula -> Bool
sonAlfaEquiv a b = igual [] a b
  --ligadas a /= ligadas b
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
termIgual :: [(Term,Term)] -> Term -> Term -> Bool
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
igual ts (ForAll a b) (ForAll c d) = (igual ((ligadas (ForAll a b), ligadas (ForAll a b)):ts) b d)
igual ts (Exists a b) (Exists c d) = (igual ((ligadas (Exists a b), ligadas (Exists a b)):ts) b d)

--igual :: [(Simbolo,Simbolo)] -> Formula -> Formula -> Bool


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

unifica :: Formula -> Formula -> [Sustitucion]
unifica a _ = []

hayResolvente :: Formula -> Formula -> Bool
hayResolvente a _ = False

resolucion :: [Formula] -> [Formula] -> [Formula]
resolucion [a] _ = []