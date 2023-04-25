module PruebasPractica03 where

import Test.QuickCheck
import LPred

-- Auxiliares
r = Var "r"
u = Var "u"
v = Var "v"
w = Var "w"
x = Var "x"
y = Var "y"
z = Var "z"

-- Ejercicio 1
prueba1 = libres ((ForAll "x" (Exists "y" (Predicado "P" [x,y]))) `And` (Predicado "Q" [x,y])) == ["x","y"]
prueba2 = libres (ForAll "x" (And (Predicado "P" [x,y]) (Exists "y" (Predicado "Q" [y,z])))) == ["y","z"]
prueba3 = libres (ForAll "x" ((Predicado "P" [x]) `Impl` (Predicado "R" [(Func "f" [x, (Func "a" [])]),x]) 
          `And` (Predicado "Q" [(Func "f" [x, (Func "a" [])]),(Func "a" [])]))) == []
-- Ejercicio 2
prueba4 = ligadas ((ForAll "x" (Predicado "P" [x,y]) `And` (ForAll "y" (Predicado "Q" [x,y])))) == ["x","y"]
prueba5 = ligadas ((ForAll "x" (ForAll "y" (Not (Predicado "P" [x,y])))) `And` (Predicado "Q" [x,y]) `Impl` 
          (Exists "x" (Exists "y" (Predicado "R" [x,y,z])))) == ["x","y"]
prueba6 = ligadas ((Predicado "P" [x,(Func "a" []), y]) `Or` (Exists "y" (Predicado "P" [x, y, (Func "a" [])]) `And` 
          (Predicado "Q" [(Func "a" []), z]))) == ["y"]

-- Ejercicio 3
prueba7 = sustv1 (ForAll "x" ((Predicado "P" [x,y]) `And` (Exists "y" (Predicado "Q" [y,z])))) ("z", (Func "g" [w,(Func "c" [])])) 
           == (ForAll "x" ((Predicado "P" [x,y]) `And` (Exists "y" (Predicado "Q" [y,(Func "g" [w,(Func "c" [])])])))) 
prueba8 = sustv1 (ForAll "x" ((Predicado "P" [x,y]) `And` (Exists "y" (Predicado "Q" [y,(Func "f" [z])])))) ("z", w) 
           == (ForAll "x" ((Predicado "P" [x,y]) `And` (Exists "y" (Predicado "Q" [y,(Func "f" [w])]))))
prueba9 = sustv1 (ForAll "x" (Exists "y" (Predicado "Q" [(Func "f" [x]),y]))) ("r",(Func "f" [z])) 
           == (ForAll "x" (Exists "y" (Predicado "Q" [(Func "f" [x]),y])))

-- Ejercicio 4
prueba10 = sonAlfaEquiv ((ForAll "x" (Predicado "P" [x,y])) `Or` (Exists "y" (Predicado "Q" [x,y,z]))) 
           ((ForAll "w" (Predicado "P" [w,y])) `Or` (Exists "v" (Predicado "Q" [x,v,z]))) == True
prueba11 = sonAlfaEquiv ((ForAll "x" (Predicado "P" [x,y])) `Or` (Exists "y" (Predicado "Q" [x,y,z]))) 
           ((ForAll "w" (Predicado "P" [w,y])) `Or` (Exists "z" (Predicado "Q" [x,z,z]))) == False
prueba12 = sonAlfaEquiv (Exists "x" ((Predicado "P" [x]) `And` (ForAll "y" ((Predicado "Q" [y]) `Impl` 
           (Not (Predicado "R" [(Func "f" [x]),y]))))))
           (Exists "y" ((Predicado "P" [y]) `And` (ForAll "x" ((Predicado "Q" [x]) `Impl` 
            (Not (Predicado "R" [(Func "f" [y]),x])))))) == True

-- Ejercicio 5
prueba13 = renombra ((ForAll "x" (Predicado "P" [x,y])) `Or` (Exists "y" (Predicado "Q" [x,y,z]))) == 
           ((ForAll "w" (Predicado "P" [w,y])) `Or` (Exists "r" (Predicado "Q" [x,r,z])))
prueba14 = renombra ((ForAll "x" (ForAll "y" (Not (Predicado "P" [x,y])))) `And` (Predicado "Q" [x,y]) `Impl`
          (Exists "x" (Exists "y" (Predicado "R" [x,y,z])))) 
           == ((ForAll "w" (ForAll "v" (Not (Predicado "P" [w,v])))) `And` (Predicado "Q" [x,y]) `Impl`
          (Exists "w" (Exists "v" (Predicado "R" [w,v,z]))))
prueba15 = renombra (ForAll "x" ((Predicado "P" [x,y]) `And` (Exists "y" (Predicado "Q" [(Func "f" [y]),z])))) 
           == (ForAll "w" ((Predicado "P" [w,y]) `And` (Exists "r" (Predicado "Q" [(Func "f" [r]),z])))) 

-- Ejercicio 6
prueba16 = sustv2 (ForAll "x" ((Predicado "P" [x,y]) `And` (Exists "y" (Predicado "Q" [y,z])))) ("z",y)
           == (ForAll "w" ((Predicado "P" [w,y]) `And` (Exists "r" (Predicado "Q" [r,y]))))
prueba17 = sustv2 (ForAll "x" ((Predicado "P" [x,y,v]) `And` (Exists "y" (Predicado "Q" [(Func "f" [y]),(Func "f" [v])])))) ("v",u) 
           == (ForAll "w" ((Predicado "P" [w,y,u]) `And` (Exists "r" (Predicado "Q" [(Func "f" [r]),(Func "f" [u])])))) 
prueba18 = sustv2 (ForAll "x" (Exists "y" (Predicado "Q" [(Func "f" [x]),y]))) ("r",(Func "f" [z])) 
           == (ForAll "x" (Exists "y" (Predicado "Q" [(Func "f" [x]),y])))

-- Ejercicio 7
prueba19 = unifica (Predicado "Q" [x,y,x]) (Predicado "Q" [(Func "f" [r,w]),(Func "g" [x]),x]) 
           == [("x",(Func "f" [r,w])),("y",(Func "g" [(Func "f" [r,w])]))] 
prueba20 = unifica (Predicado "Q" [(Func "a" []),(Func "c" []),(Func "f" [x])]) (Predicado "Q" [z,(Func "c" []),v]) 
           == [("z",(Func "a" [])),("v",(Func "f" [x]))]
prueba21 = unifica (Predicado "P" [(Func "f" [x,y])]) (Predicado "P" [(Func "f" [(Func "a" []),(Func "b" [])])]) 
           == [("x",(Func "a" [])), ("y",(Func "b" []))]

-- Ejercicio 8
prueba22 = hayResolvente ((Not (Predicado "P" [x])) `Or` (Predicado "Q" [(Func "f" [x])])) 
          ((Predicado "P" [y]) `Or` (Not (Predicado "R" [(Func "f" [x])])))  == False
prueba23 = hayResolvente ((Predicado "P" [x]) `Or` (Predicado "Q" [(Func "f" [x])])) 
          ((Predicado "P" [z]) `Or` (Not (Predicado "Q" [(Func "f" [y])]))) == True
prueba24 = hayResolvente ((Predicado "P" [x,y]) `Or` (Not (Predicado "Q" [(Func "a" []),x]))) 
          ((Predicado "R" [z]) `Or` (Predicado "Q" [z,(Func "b" [])]))  == True

-- Ejercicio 9
prueba25 = resolucion [(Predicado "Q" [x,y,x])] [(Predicado "Q" [y,(Func "g" [x]),x])]  == []
prueba26 = resolucion [(Predicado "P" [x]),(Predicado "Q" [(Func "f" [x])])] 
           [(Predicado "P" [z]),(Not (Predicado "Q" [(Func "f" [y])]))] == [(Predicado "P" [y]),(Predicado "P" [z])]
prueba27 = resolucion [(Predicado "P" [x,y]),(Not (Predicado "Q" [(Func "a" []),x]))] 
           [(Predicado "R" [z]),(Predicado "Q" [z,(Func "b" [])])]  
           == [(Predicado "P" [(Func "b" []),y]),(Predicado "R" [(Func "a" [])])]


correctas = length $ filter (== True) [prueba1,prueba2,prueba3,prueba4,prueba5,prueba6,prueba7,prueba8,
                                       prueba9,prueba10,prueba11,prueba12,prueba13,prueba14,prueba15,prueba16,
                                       prueba17,prueba18,prueba19,prueba20,prueba21,prueba22,prueba23,prueba24,
                                       prueba25,prueba26,prueba27]
calificacion = (fromIntegral correctas :: Float) * 10 / 27

run = do putStr "Prueba 1:  " 
         quickCheck prueba1
         putStr "Prueba 2:  "
         quickCheck prueba2
         putStr "Prueba 3:  "
         quickCheck prueba3
         putStr "Prueba 4:  "
         quickCheck prueba4
         putStr "Prueba 5:  "
         quickCheck prueba5
         putStr "Prueba 6:  "
         quickCheck prueba6
         putStr "Prueba 7:  "
         quickCheck prueba7
         putStr "Prueba 8:  "
         quickCheck prueba8
         putStr "Prueba 9:  "
         quickCheck prueba9
         putStr "Prueba 10: "
         quickCheck prueba10
         putStr "Prueba 11: "
         quickCheck prueba11
         putStr "Prueba 12: "
         quickCheck prueba12
         putStr "Prueba 13: "
         quickCheck prueba13
         putStr "Prueba 14: "
         quickCheck prueba14
         putStr "Prueba 15: "
         quickCheck prueba15
         putStr "Prueba 16: " 
         quickCheck prueba16
         putStr "Prueba 17: "
         quickCheck prueba17
         putStr "Prueba 18: "
         quickCheck prueba18
         putStr "Prueba 19: "
         quickCheck prueba19
         putStr "Prueba 20: "
         quickCheck prueba20
         putStr "Prueba 21: "
         quickCheck prueba21
         putStr "Prueba 22: "
         quickCheck prueba22
         putStr "Prueba 23: "
         quickCheck prueba23
         putStr "Prueba 24: "
         quickCheck prueba24
         putStr "Prueba 25: "
         quickCheck prueba25
         putStr "Prueba 26: "
         quickCheck prueba26
         putStr "Prueba 27: "
         quickCheck prueba27
         putStr "\nCalificación: "
         putStr ((show calificacion) ++ "\n")
