module Issue1906_branch where

data Bool : Set where
  true : Bool
  false : Bool

data F (n : Bool) : Set where
  f : F n

module B (a : Bool) where
  b1 : F a
  b1 = f

xor : Bool -> Bool -> Bool
xor true true = false
xor false true = true
xor true false = true
xor false false = false

mash : {a : Bool} {b : Bool} -> F a -> F b -> F (xor a b)
mash f f = f

p1 : F false
p1 = a
  where
    open B _

    a0 : F _
    a0 = b1

    a1 : F _
    a1 = a0
    a2 : F _
    a2 = mash a1 a0
    a3 : F _
    a3 = mash a2 a1
    a4 : F _
    a4 = mash a3 a2
    a5 : F _
    a5 = mash a4 a3
    a6 : F _
    a6 = mash a5 a4
    a7 : F _
    a7 = mash a6 a5
    a8 : F _
    a8 = mash a7 a6
    a9 : F _
    a9 = mash a8 a7
    a10 : F _
    a10 = mash a9 a8
    a11 : F _
    a11 = mash a10 a9
    a12 : F _
    a12 = mash a11 a10
    a13 : F _
    a13 = mash a12 a11
    a14 : F _
    a14 = mash a13 a12
    a15 : F _
    a15 = mash a14 a13
    a16 : F _
    a16 = mash a15 a14
    a17 : F _
    a17 = mash a16 a15
    a18 : F _
    a18 = mash a17 a16
    a19 : F _
    a19 = mash a18 a17
    a20 : F _
    a20 = mash a19 a18
    a21 : F _
    a21 = mash a20 a19
    a22 : F _
    a22 = mash a21 a20
    a23 : F _
    a23 = mash a22 a21
    a24 : F _
    a24 = mash a23 a22
    a : F _
    a = a0
