#eval (1 - 2 : Int)

#check (1 - 2 : Int)

def hello := "Hello, World!"

#eval hello

def add1 (n : Nat) : Nat := n + 1

def choose (flag : Bool) (a b : Nat) : Nat :=
  if flag then a else b

#eval choose true 1 2
#eval choose false 1 2
#check add1

def maximum (n : Nat) (k : Nat) : Nat :=
  if n < k then
    k
  else n

#check (maximum)

def square (x : Nat) : Nat :=
  x * x

def g (h : Nat → Nat) : Nat :=
  h 5

#eval g square

def joinStringWith (separator : String) (s1 : String) (s2 : String) : String :=
  s1 ++ separator ++ s2

#eval joinStringWith ", " "Hello" "World"
#check (joinStringWith ": ")

def volume (l : Nat) (w : Nat) (h : Nat) : Nat :=
  l * w * h

#eval volume 1 2 3
#check (volume)

def Str : Type := String

def aStr : Str := "Hello, World!"

#eval aStr
#check (aStr)

def NaturalNumber : Type := Nat
