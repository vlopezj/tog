------------------------------------------------------------------------
-- A small definition of a dependently typed language, using the
-- technique from McBride's "Outrageous but Meaningful Coincidences"
------------------------------------------------------------------------

{-# OPTIONS --type-in-type #-}

-- The code contains an example, a partial definition of categories,
-- which triggers the use of an enormous amount of memory (with the
-- development version of Agda which is current at the time of
-- writing). I'm not entirely sure if the code is correct: 2.5G heap
-- doesn't seem to suffice to typecheck this code. /NAD

module Language_test3 where

------------------------------------------------------------------------
-- Prelude

{-@AGDA-}
open import Prelude

subst : {A : Set} {x y : A} (P : A -> Set) ->
        x == y -> P x -> P y
subst P = J (\ x y _ -> P x -> P y) (\ x p -> p)

Empty : Set
Empty = (A : Set) -> A

record Unit : Set
record Unit where
  constructor tt

{-@AGDA-}
open Unit

data Either (A : Set) (B : Set) : Set
data Either A B where
  left  : A -> Either A B
  right : B -> Either A B

record Sigma (A : Set) (B : A -> Set) : Set
record Sigma A B where
  constructor pair
  field
    fst : A
    snd : B fst

{-@AGDA-}
open Sigma

uncurry : {A : Set} {B : A -> Set} {C : Sigma A B -> Set} ->
          ((x : A) (y : B x) -> C (pair x y)) ->
          ((p : Sigma A B) -> C p)
uncurry f p = f (fst p) (snd p)

Times : Set -> Set -> Set
Times A B = Sigma A (\ _ -> B)

------------------------------------------------------------------------
-- A universe

data U : Set

El : U -> Set

data U where
  set   : U
  el    : Set -> U
  sigma : (a : U) -> (El a -> U) -> U
  pi    : (a : U) -> (El a -> U) -> U

El set         = Set
El (el A)      = A
El (sigma a b) = Sigma (El a) (\ x -> El (b x))
El (pi a b)    = (x : El a) -> El (b x)

-- Abbreviations.

fun : U -> U -> U
fun a b = pi a (\ _ -> b)

times : U -> U -> U
times a b = sigma a (\ _ -> b)

-- Example.

------------------------------------------------------------------------
-- Contexts

-- Contexts.

data Ctxt : Set

-- Types.

Ty : Ctxt -> Set

-- Environments.

Env : Ctxt -> Set

data Ctxt where
  empty : Ctxt
  snoc  : (G : Ctxt) -> Ty G -> Ctxt

Ty G = Env G -> U

Env empty      = Unit
Env (snoc G s) = Sigma (Env G) (\ g -> El (s g))

-- Variables (de Bruijn indices).

Var : (G : Ctxt) -> Ty G -> Set
Var empty      t = Empty
Var (snoc G s) t =
  Either ((\ g -> s (fst g)) == t)
         (Sigma _ (\ u -> Times ((\ g -> u (fst g)) == t) (Var G u)))

zero : {G : _} {s : _} ->
       Var (snoc G s) (\ g -> s (fst g))
zero = left refl

suc : {G : _} {s : _} {t : _}
      (x : Var G t) ->
      Var (snoc G s) (\ g -> t (fst g))
suc x = right (pair _ (pair refl x))

-- A lookup function.

lookup : (G : Ctxt) (s : Ty G) -> Var G s -> (g : Env G) -> El (s g)
lookup empty      _ absurd     _ = absurd _
lookup (snoc _ _) _ (left  eq) g = subst (\ f -> El (f g)) eq (snd g)
lookup (snoc _ _) t (right p)  g =
  subst (\ f -> El (f g)) (fst (snd p)) (lookup _ _ (snd (snd p)) (fst g))

------------------------------------------------------------------------
-- A language

-- Syntax for types.

data Type (G : Ctxt) (s : Ty G) : Set

-- Terms.

data Term (G : Ctxt) (s : Ty G) : Set

-- The semantics of a term.

eval : {G : _} {s : _} -> Term G s -> (g : Env G) -> El (s g)

data Type G s where
  set''   : s == (\ _ -> set) -> Type G s
  el''    : (x : Term G (\ _ -> set)) ->
            (\ g -> el (eval x g)) == s ->
            Type G s
  sigma'' : {t : _} {u : _} ->
            Type G t ->
            Type (snoc G t) u ->
            (\ g -> sigma (t g) (\ v -> u (pair g v))) == s ->
            Type G s
  pi''    : {t : _} {u : _} ->
            Type G t ->
            Type (snoc G t) u ->
            (\ g -> pi (t g) (\ v -> u (pair g v))) == s ->
            Type G s

data Term G s where
  var   : Var G s -> Term G s
  lam'' : {t : _} {u : _} ->
          Term (snoc G t) (uncurry u) ->
          (\ g -> pi (t g) (\ v -> u g v)) == s ->
          Term G s
  app'' : {t : _} {u : (g : Env G) -> El (t g) -> U} ->
          Term G (\ g -> pi (t g) (\ v -> u g v)) ->
          (t2 : Term G t) ->
          (\ g -> u g (eval t2 g)) == s ->
          Term G s

eval (var x)          g = lookup _ _ x g
eval (lam'' t eq)     g = subst (\ f -> El (f g)) eq
                            (\ v -> eval t (pair g v))
eval (app'' t1 t2 eq) g = subst (\ f -> El (f g)) eq
                            (eval t1 g (eval t2 g))

-- Abbreviations.

set' : {G : _} -> Type G (\ _ -> set)
set' = set'' refl

el' : {G : _}
      (x : Term G (\ _ -> set)) ->
      Type G (\ g -> el (eval x g))
el' x = el'' x refl

sigma' : {G : _} {t : _} {u : _} ->
         Type G t ->
         Type (snoc G t) u ->
         Type G (\ g -> sigma (t g) (\ v -> u (pair g v)))
sigma' s t = sigma'' s t refl

pi' : {G : _} {t : _} {u : _} ->
      Type G t ->
      Type (snoc G t) u ->
      Type G (\ g -> pi (t g) (\ v -> u (pair g v)))
pi' s t = pi'' s t refl

lam : {G : _} {t : _} {u : _} ->
      Term (snoc G t) (uncurry u) ->
      Term G (\ g -> pi (t g) (\ v -> u g v))
lam t = lam'' t refl

app : {G : _} {t : _} {u : (g : Env G) -> El (t g) -> U} ->
      Term G (\ g -> pi (t g) (\ v -> u g v)) ->
      (t2 : Term G t) ->
      Term G (\ g -> u g (eval t2 g))
app t1 t2 = app'' t1 t2 refl

-- Example.

raw-categoryU : U
raw-categoryU =
  sigma set (\ obj ->
  sigma (fun (el obj) (fun (el obj) set)) (\ hom ->
  (pi (el obj) (\ x -> el (hom x x)))))

raw-category : Type empty (\ _ -> raw-categoryU)
raw-category =
     -- Objects.
   sigma' {empty} {\_ -> set} {\ g ->
                                   sigma
                                   (pi
                                    (el
                                     (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                      (var (zero {empty} {\ _ -> set})) g))
                                    (\ v ->
                                       pi
                                       (el
                                        (eval
                                         {snoc (snoc empty (\ _ -> set))
                                          (\ g1 ->
                                             el
                                             (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                              (var (zero {empty} {\ _ -> set})) g1))}
                                         {\ _ -> set}
                                         (var
                                          (suc {snoc empty (\ _ -> set)}
                                           {\ z ->
                                              el
                                              (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                               (var (zero {empty} {\ _ -> set})) z)}
                                           {\ _ -> set} (zero {empty} {\ _ -> set})))
                                         (pair g v)))
                                       (\ v1 -> set)))
                                   (\ v ->
                                      pi
                                      (el
                                       (eval
                                        {snoc (snoc empty (\ _ -> set))
                                         (\ z ->
                                            pi
                                            (el
                                             (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                              (var (zero {empty} {\ _ -> set})) z))
                                            (\ v1 ->
                                               pi
                                               (el
                                                (eval
                                                 {snoc (snoc empty (\ _ -> set))
                                                  (\ g1 ->
                                                     el
                                                     (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                      (var (zero {empty} {\ _ -> set})) g1))}
                                                 {\ _ -> set}
                                                 (var
                                                  (suc {snoc empty (\ _ -> set)}
                                                   {\ z1 ->
                                                      el
                                                      (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                       (var (zero {empty} {\ _ -> set})) z1)}
                                                   {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                 (pair z v1)))
                                               (\ v1 -> set)))}
                                        {\ _ -> set}
                                        (var
                                         (suc {snoc empty (\ _ -> set)}
                                          {\ z ->
                                             pi
                                             (el
                                              (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                               (var (zero {empty} {\ _ -> set})) z))
                                             (\ v1 ->
                                                pi
                                                (el
                                                 (eval
                                                  {snoc (snoc empty (\ _ -> set))
                                                   (\ g1 ->
                                                      el
                                                      (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                       (var (zero {empty} {\ _ -> set})) g1))}
                                                  {\ _ -> set}
                                                  (var
                                                   (suc {snoc empty (\ _ -> set)}
                                                    {\ z1 ->
                                                       el
                                                       (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                        (var (zero {empty} {\ _ -> set})) z1)}
                                                    {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                  (pair z v1)))
                                                (\ v1 -> set))}
                                          {\ g1 -> set} (zero {empty} {\ _ -> set})))
                                        (pair g v)))
                                      (\ v1 ->
                                         el
                                         (eval
                                          {snoc
                                           (snoc (snoc empty (\ _ -> set))
                                            (\ z ->
                                               pi
                                               (el
                                                (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                 (var (zero {empty} {\ _ -> set})) z))
                                               (\ v1 ->
                                                  pi
                                                  (el
                                                   (eval
                                                    {snoc (snoc empty (\ _ -> set))
                                                     (\ g1 ->
                                                        el
                                                        (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                         (var (zero {empty} {\ _ -> set})) g1))}
                                                    {\ _ -> set}
                                                    (var
                                                     (suc {snoc empty (\ _ -> set)}
                                                      {\ z1 ->
                                                         el
                                                         (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                          (var (zero {empty} {\ _ -> set})) z1)}
                                                      {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                    (pair z v1)))
                                                  (\ v2 -> set))))
                                           (\ z ->
                                              el
                                              (eval
                                               {snoc (snoc empty (\ _ -> set))
                                                (\ z1 ->
                                                   pi
                                                   (el
                                                    (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                     (var (zero {empty} {\ _ -> set})) z1))
                                                   (\ v1 ->
                                                      pi
                                                      (el
                                                       (eval
                                                        {snoc (snoc empty (\ _ -> set))
                                                         (\ g1 ->
                                                            el
                                                            (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                             (var (zero {empty} {\ _ -> set})) g1))}
                                                        {\ _ -> set}
                                                        (var
                                                         (suc {snoc empty (\ _ -> set)}
                                                          {\ z2 ->
                                                             el
                                                             (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                              (var (zero {empty} {\ _ -> set})) z2)}
                                                          {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                        (pair z1 v1)))
                                                      (\ v2 -> set)))}
                                               {\ _ -> set}
                                               (var
                                                (suc {snoc empty (\ _ -> set)}
                                                 {\ z1 ->
                                                    pi
                                                    (el
                                                     (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                      (var (zero {empty} {\ _ -> set})) z1))
                                                    (\ v1 ->
                                                       pi
                                                       (el
                                                        (eval
                                                         {snoc (snoc empty (\ _ -> set))
                                                          (\ g1 ->
                                                             el
                                                             (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                              (var (zero {empty} {\ _ -> set})) g1))}
                                                         {\ _ -> set}
                                                         (var
                                                          (suc {snoc empty (\ _ -> set)}
                                                           {\ z2 ->
                                                              el
                                                              (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                               (var (zero {empty} {\ _ -> set})) z2)}
                                                           {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                         (pair z1 v1)))
                                                       (\ v2 -> set))}
                                                 {\ g1 -> set} (zero {empty} {\ _ -> set})))
                                               z))}
                                          {\ _ -> set}
                                          (app
                                           {snoc
                                            (snoc (snoc empty (\ _ -> set))
                                             (\ z ->
                                                pi
                                                (el
                                                 (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                  (var (zero {empty} {\ _ -> set})) z))
                                                (\ v1 ->
                                                   pi
                                                   (el
                                                    (eval
                                                     {snoc (snoc empty (\ _ -> set))
                                                      (\ g1 ->
                                                         el
                                                         (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                          (var (zero {empty} {\ _ -> set})) g1))}
                                                     {\ _ -> set}
                                                     (var
                                                      (suc {snoc empty (\ _ -> set)}
                                                       {\ z1 ->
                                                          el
                                                          (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                           (var (zero {empty} {\ _ -> set})) z1)}
                                                       {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                     (pair z v1)))
                                                   (\ v2 -> set))))
                                            (\ z ->
                                               el
                                               (eval
                                                {snoc (snoc empty (\ _ -> set))
                                                 (\ z1 ->
                                                    pi
                                                    (el
                                                     (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                      (var (zero {empty} {\ _ -> set})) z1))
                                                    (\ v1 ->
                                                       pi
                                                       (el
                                                        (eval
                                                         {snoc (snoc empty (\ _ -> set))
                                                          (\ g1 ->
                                                             el
                                                             (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                              (var (zero {empty} {\ _ -> set})) g1))}
                                                         {\ _ -> set}
                                                         (var
                                                          (suc {snoc empty (\ _ -> set)}
                                                           {\ z2 ->
                                                              el
                                                              (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                               (var (zero {empty} {\ _ -> set})) z2)}
                                                           {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                         (pair z1 v1)))
                                                       (\ v2 -> set)))}
                                                {\ _ -> set}
                                                (var
                                                 (suc {snoc empty (\ _ -> set)}
                                                  {\ z1 ->
                                                     pi
                                                     (el
                                                      (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                       (var (zero {empty} {\ _ -> set})) z1))
                                                     (\ v1 ->
                                                        pi
                                                        (el
                                                         (eval
                                                          {snoc (snoc empty (\ _ -> set))
                                                           (\ g1 ->
                                                              el
                                                              (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                               (var (zero {empty} {\ _ -> set})) g1))}
                                                          {\ _ -> set}
                                                          (var
                                                           (suc {snoc empty (\ _ -> set)}
                                                            {\ z2 ->
                                                               el
                                                               (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                (var (zero {empty} {\ _ -> set})) z2)}
                                                            {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                          (pair z1 v1)))
                                                        (\ v2 -> set))}
                                                  {\ g1 -> set} (zero {empty} {\ _ -> set})))
                                                z))}
                                           {\ g1 ->
                                              el
                                              (eval
                                               {snoc (snoc empty (\ _ -> set))
                                                (\ z ->
                                                   pi
                                                   (el
                                                    (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                     (var (zero {empty} {\ _ -> set})) z))
                                                   (\ v1 ->
                                                      pi
                                                      (el
                                                       (eval
                                                        {snoc (snoc empty (\ _ -> set))
                                                         (\ g2 ->
                                                            el
                                                            (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                             (var (zero {empty} {\ _ -> set})) g2))}
                                                        {\ _ -> set}
                                                        (var
                                                         (suc {snoc empty (\ _ -> set)}
                                                          {\ z1 ->
                                                             el
                                                             (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                              (var (zero {empty} {\ _ -> set})) z1)}
                                                          {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                        (pair z v1)))
                                                      (\ v2 -> set)))}
                                               {\ _ -> set}
                                               (var
                                                (suc {snoc empty (\ _ -> set)}
                                                 {\ z ->
                                                    pi
                                                    (el
                                                     (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                      (var (zero {empty} {\ _ -> set})) z))
                                                    (\ v1 ->
                                                       pi
                                                       (el
                                                        (eval
                                                         {snoc (snoc empty (\ _ -> set))
                                                          (\ g2 ->
                                                             el
                                                             (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                              (var (zero {empty} {\ _ -> set})) g2))}
                                                         {\ _ -> set}
                                                         (var
                                                          (suc {snoc empty (\ _ -> set)}
                                                           {\ z1 ->
                                                              el
                                                              (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                               (var (zero {empty} {\ _ -> set})) z1)}
                                                           {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                         (pair z v1)))
                                                       (\ v2 -> set))}
                                                 {\ g2 -> set} (zero {empty} {\ _ -> set})))
                                               (fst g1))}
                                           {\ g1 v1 -> set}
                                           (app
                                            {snoc
                                             (snoc (snoc empty (\ _ -> set))
                                              (\ z ->
                                                 pi
                                                 (el
                                                  (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                   (var (zero {empty} {\ _ -> set})) z))
                                                 (\ v1 ->
                                                    pi
                                                    (el
                                                     (eval
                                                      {snoc (snoc empty (\ _ -> set))
                                                       (\ g1 ->
                                                          el
                                                          (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                           (var (zero {empty} {\ _ -> set})) g1))}
                                                      {\ _ -> set}
                                                      (var
                                                       (suc {snoc empty (\ _ -> set)}
                                                        {\ z1 ->
                                                           el
                                                           (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                            (var (zero {empty} {\ _ -> set})) z1)}
                                                        {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                      (pair z v1)))
                                                    (\ v2 -> set))))
                                             (\ z ->
                                                el
                                                (eval
                                                 {snoc (snoc empty (\ _ -> set))
                                                  (\ z1 ->
                                                     pi
                                                     (el
                                                      (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                       (var (zero {empty} {\ _ -> set})) z1))
                                                     (\ v1 ->
                                                        pi
                                                        (el
                                                         (eval
                                                          {snoc (snoc empty (\ _ -> set))
                                                           (\ g1 ->
                                                              el
                                                              (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                               (var (zero {empty} {\ _ -> set})) g1))}
                                                          {\ _ -> set}
                                                          (var
                                                           (suc {snoc empty (\ _ -> set)}
                                                            {\ z2 ->
                                                               el
                                                               (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                (var (zero {empty} {\ _ -> set})) z2)}
                                                            {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                          (pair z1 v1)))
                                                        (\ v2 -> set)))}
                                                 {\ _ -> set}
                                                 (var
                                                  (suc {snoc empty (\ _ -> set)}
                                                   {\ z1 ->
                                                      pi
                                                      (el
                                                       (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                        (var (zero {empty} {\ _ -> set})) z1))
                                                      (\ v1 ->
                                                         pi
                                                         (el
                                                          (eval
                                                           {snoc (snoc empty (\ _ -> set))
                                                            (\ g1 ->
                                                               el
                                                               (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                (var (zero {empty} {\ _ -> set})) g1))}
                                                           {\ _ -> set}
                                                           (var
                                                            (suc {snoc empty (\ _ -> set)}
                                                             {\ z2 ->
                                                                el
                                                                (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                 (var (zero {empty} {\ _ -> set})) z2)}
                                                             {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                           (pair z1 v1)))
                                                         (\ v2 -> set))}
                                                   {\ g1 -> set} (zero {empty} {\ _ -> set})))
                                                 z))}
                                            {\ g1 ->
                                               el
                                               (eval
                                                {snoc (snoc empty (\ _ -> set))
                                                 (\ z ->
                                                    pi
                                                    (el
                                                     (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                      (var (zero {empty} {\ _ -> set})) z))
                                                    (\ v1 ->
                                                       pi
                                                       (el
                                                        (eval
                                                         {snoc (snoc empty (\ _ -> set))
                                                          (\ g2 ->
                                                             el
                                                             (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                              (var (zero {empty} {\ _ -> set})) g2))}
                                                         {\ _ -> set}
                                                         (var
                                                          (suc {snoc empty (\ _ -> set)}
                                                           {\ z1 ->
                                                              el
                                                              (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                               (var (zero {empty} {\ _ -> set})) z1)}
                                                           {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                         (pair z v1)))
                                                       (\ v2 -> set)))}
                                                {\ _ -> set}
                                                (var
                                                 (suc {snoc empty (\ _ -> set)}
                                                  {\ z ->
                                                     pi
                                                     (el
                                                      (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                       (var (zero {empty} {\ _ -> set})) z))
                                                     (\ v1 ->
                                                        pi
                                                        (el
                                                         (eval
                                                          {snoc (snoc empty (\ _ -> set))
                                                           (\ g2 ->
                                                              el
                                                              (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                               (var (zero {empty} {\ _ -> set})) g2))}
                                                          {\ _ -> set}
                                                          (var
                                                           (suc {snoc empty (\ _ -> set)}
                                                            {\ z1 ->
                                                               el
                                                               (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                (var (zero {empty} {\ _ -> set})) z1)}
                                                            {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                          (pair z v1)))
                                                        (\ v2 -> set))}
                                                  {\ g2 -> set} (zero {empty} {\ _ -> set})))
                                                (fst g1))}
                                            {\ g1 v1 ->
                                               pi
                                               (el
                                                (eval
                                                 {snoc (snoc empty (\ _ -> set))
                                                  (\ g2 ->
                                                     el
                                                     (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                      (var (zero {empty} {\ _ -> set})) g2))}
                                                 {\ _ -> set}
                                                 (var
                                                  (suc {snoc empty (\ _ -> set)}
                                                   {\ z ->
                                                      el
                                                      (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                       (var (zero {empty} {\ _ -> set})) z)}
                                                   {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                 (pair (fst (fst g1)) v1)))
                                               (\ v2 -> set)}
                                            (var
                                             (suc
                                              {snoc (snoc empty (\ _ -> set))
                                               (\ z ->
                                                  pi
                                                  (el
                                                   (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                    (var (zero {empty} {\ _ -> set})) z))
                                                  (\ v1 ->
                                                     pi
                                                     (el
                                                      (eval
                                                       {snoc (snoc empty (\ _ -> set))
                                                        (\ g1 ->
                                                           el
                                                           (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                            (var (zero {empty} {\ _ -> set})) g1))}
                                                       {\ _ -> set}
                                                       (var
                                                        (suc {snoc empty (\ _ -> set)}
                                                         {\ z1 ->
                                                            el
                                                            (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                             (var (zero {empty} {\ _ -> set})) z1)}
                                                         {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                       (pair z v1)))
                                                     (\ v2 -> set)))}
                                              {\ z ->
                                                 el
                                                 (eval
                                                  {snoc (snoc empty (\ _ -> set))
                                                   (\ z1 ->
                                                      pi
                                                      (el
                                                       (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                        (var (zero {empty} {\ _ -> set})) z1))
                                                      (\ v1 ->
                                                         pi
                                                         (el
                                                          (eval
                                                           {snoc (snoc empty (\ _ -> set))
                                                            (\ g1 ->
                                                               el
                                                               (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                (var (zero {empty} {\ _ -> set})) g1))}
                                                           {\ _ -> set}
                                                           (var
                                                            (suc {snoc empty (\ _ -> set)}
                                                             {\ z2 ->
                                                                el
                                                                (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                 (var (zero {empty} {\ _ -> set})) z2)}
                                                             {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                           (pair z1 v1)))
                                                         (\ v2 -> set)))}
                                                  {\ _ -> set}
                                                  (var
                                                   (suc {snoc empty (\ _ -> set)}
                                                    {\ z1 ->
                                                       pi
                                                       (el
                                                        (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                         (var (zero {empty} {\ _ -> set})) z1))
                                                       (\ v1 ->
                                                          pi
                                                          (el
                                                           (eval
                                                            {snoc (snoc empty (\ _ -> set))
                                                             (\ g1 ->
                                                                el
                                                                (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                 (var (zero {empty} {\ _ -> set})) g1))}
                                                            {\ _ -> set}
                                                            (var
                                                             (suc {snoc empty (\ _ -> set)}
                                                              {\ z2 ->
                                                                 el
                                                                 (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                  (var (zero {empty} {\ _ -> set})) z2)}
                                                              {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                            (pair z1 v1)))
                                                          (\ v2 -> set))}
                                                    {\ g1 -> set} (zero {empty} {\ _ -> set})))
                                                  z)}
                                              {\ g1 ->
                                                 pi
                                                 (el
                                                  (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                   (var (zero {empty} {\ _ -> set})) (fst g1)))
                                                 (\ v1 ->
                                                    pi
                                                    (el
                                                     (eval
                                                      {snoc (snoc empty (\ _ -> set))
                                                       (\ g2 ->
                                                          el
                                                          (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                           (var (zero {empty} {\ _ -> set})) g2))}
                                                      {\ _ -> set}
                                                      (var
                                                       (suc {snoc empty (\ _ -> set)}
                                                        {\ z ->
                                                           el
                                                           (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                            (var (zero {empty} {\ _ -> set})) z)}
                                                        {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                      (pair (fst g1) v1)))
                                                    (\ v2 -> set))}
                                              (zero {snoc empty (\ _ -> set)}
                                               {\ z ->
                                                  pi
                                                  (el
                                                   (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                    (var (zero {empty} {\ _ -> set})) z))
                                                  (\ v1 ->
                                                     pi
                                                     (el
                                                      (eval
                                                       {snoc (snoc empty (\ _ -> set))
                                                        (\ g1 ->
                                                           el
                                                           (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                            (var (zero {empty} {\ _ -> set})) g1))}
                                                       {\ _ -> set}
                                                       (var
                                                        (suc {snoc empty (\ _ -> set)}
                                                         {\ z1 ->
                                                            el
                                                            (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                             (var (zero {empty} {\ _ -> set})) z1)}
                                                         {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                       (pair z v1)))
                                                     (\ v2 -> set))})))
                                            (var
                                             (zero
                                              {snoc (snoc empty (\ v1 -> set))
                                               (\ z ->
                                                  pi
                                                  (el
                                                   (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                    (var (zero {empty} {\ _ -> set})) z))
                                                  (\ v1 ->
                                                     pi
                                                     (el
                                                      (eval
                                                       {snoc (snoc empty (\ _ -> set))
                                                        (\ g1 ->
                                                           el
                                                           (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                            (var (zero {empty} {\ _ -> set})) g1))}
                                                       {\ _ -> set}
                                                       (var
                                                        (suc {snoc empty (\ _ -> set)}
                                                         {\ z1 ->
                                                            el
                                                            (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                             (var (zero {empty} {\ _ -> set})) z1)}
                                                         {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                       (pair z v1)))
                                                     (\ v2 -> set)))}
                                              {\ z ->
                                                 el
                                                 (eval
                                                  {snoc (snoc empty (\ _ -> set))
                                                   (\ z1 ->
                                                      pi
                                                      (el
                                                       (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                        (var (zero {empty} {\ _ -> set})) z1))
                                                      (\ v1 ->
                                                         pi
                                                         (el
                                                          (eval
                                                           {snoc (snoc empty (\ _ -> set))
                                                            (\ g1 ->
                                                               el
                                                               (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                (var (zero {empty} {\ _ -> set})) g1))}
                                                           {\ _ -> set}
                                                           (var
                                                            (suc {snoc empty (\ _ -> set)}
                                                             {\ z2 ->
                                                                el
                                                                (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                 (var (zero {empty} {\ _ -> set})) z2)}
                                                             {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                           (pair z1 v1)))
                                                         (\ v2 -> set)))}
                                                  {\ _ -> set}
                                                  (var
                                                   (suc {snoc empty (\ _ -> set)}
                                                    {\ z1 ->
                                                       pi
                                                       (el
                                                        (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                         (var (zero {empty} {\ _ -> set})) z1))
                                                       (\ v1 ->
                                                          pi
                                                          (el
                                                           (eval
                                                            {snoc (snoc empty (\ _ -> set))
                                                             (\ g1 ->
                                                                el
                                                                (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                 (var (zero {empty} {\ _ -> set})) g1))}
                                                            {\ _ -> set}
                                                            (var
                                                             (suc {snoc empty (\ _ -> set)}
                                                              {\ z2 ->
                                                                 el
                                                                 (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                  (var (zero {empty} {\ _ -> set})) z2)}
                                                              {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                            (pair z1 v1)))
                                                          (\ v2 -> set))}
                                                    {\ g1 -> set} (zero {empty} {\ _ -> set})))
                                                  z)})))
                                           (var
                                            (zero
                                             {snoc (snoc empty (\ v1 -> set))
                                              (\ z ->
                                                 pi
                                                 (el
                                                  (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                   (var (zero {empty} {\ _ -> set})) z))
                                                 (\ v1 ->
                                                    pi
                                                    (el
                                                     (eval
                                                      {snoc (snoc empty (\ _ -> set))
                                                       (\ g1 ->
                                                          el
                                                          (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                           (var (zero {empty} {\ _ -> set})) g1))}
                                                      {\ _ -> set}
                                                      (var
                                                       (suc {snoc empty (\ _ -> set)}
                                                        {\ z1 ->
                                                           el
                                                           (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                            (var (zero {empty} {\ _ -> set})) z1)}
                                                        {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                      (pair z v1)))
                                                    (\ v2 -> set)))}
                                             {\ z ->
                                                el
                                                (eval
                                                 {snoc (snoc empty (\ _ -> set))
                                                  (\ z1 ->
                                                     pi
                                                     (el
                                                      (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                       (var (zero {empty} {\ _ -> set})) z1))
                                                     (\ v1 ->
                                                        pi
                                                        (el
                                                         (eval
                                                          {snoc (snoc empty (\ _ -> set))
                                                           (\ g1 ->
                                                              el
                                                              (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                               (var (zero {empty} {\ _ -> set})) g1))}
                                                          {\ _ -> set}
                                                          (var
                                                           (suc {snoc empty (\ _ -> set)}
                                                            {\ z2 ->
                                                               el
                                                               (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                (var (zero {empty} {\ _ -> set})) z2)}
                                                            {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                          (pair z1 v1)))
                                                        (\ v2 -> set)))}
                                                 {\ _ -> set}
                                                 (var
                                                  (suc {snoc empty (\ _ -> set)}
                                                   {\ z1 ->
                                                      pi
                                                      (el
                                                       (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                        (var (zero {empty} {\ _ -> set})) z1))
                                                      (\ v1 ->
                                                         pi
                                                         (el
                                                          (eval
                                                           {snoc (snoc empty (\ _ -> set))
                                                            (\ g1 ->
                                                               el
                                                               (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                (var (zero {empty} {\ _ -> set})) g1))}
                                                           {\ _ -> set}
                                                           (var
                                                            (suc {snoc empty (\ _ -> set)}
                                                             {\ z2 ->
                                                                el
                                                                (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                 (var (zero {empty} {\ _ -> set})) z2)}
                                                             {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                           (pair z1 v1)))
                                                         (\ v2 -> set))}
                                                   {\ g1 -> set} (zero {empty} {\ _ -> set})))
                                                 z)})))
                                          (pair (pair g v) v1))))} set'
     -- Morphisms.
  (sigma' {snoc empty (\ _ -> set)} {\ g ->
                                        pi
                                        (el
                                         (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                          (var (zero {empty} {\ _ -> set})) g))
                                        (\ v ->
                                           pi
                                           (el
                                            (eval
                                             {snoc (snoc empty (\ _ -> set))
                                              (\ g1 ->
                                                 el
                                                 (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                  (var (zero {empty} {\ _ -> set})) g1))}
                                             {\ _ -> set}
                                             (var
                                              (suc {snoc empty (\ _ -> set)}
                                               {\ z ->
                                                  el
                                                  (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                   (var (zero {empty} {\ _ -> set})) z)}
                                               {\ _ -> set} (zero {empty} {\ _ -> set})))
                                             (pair g v)))
                                           (\ v1 -> set))} {\ g ->
                                                               pi
                                                               (el
                                                                (eval
                                                                 {snoc (snoc empty (\ _ -> set))
                                                                  (\ z ->
                                                                     pi
                                                                     (el
                                                                      (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                       (var (zero {empty} {\ _ -> set})) z))
                                                                     (\ v ->
                                                                        pi
                                                                        (el
                                                                         (eval
                                                                          {snoc (snoc empty (\ _ -> set))
                                                                           (\ g1 ->
                                                                              el
                                                                              (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                               (var (zero {empty} {\ _ -> set})) g1))}
                                                                          {\ _ -> set}
                                                                          (var
                                                                           (suc {snoc empty (\ _ -> set)}
                                                                            {\ z1 ->
                                                                               el
                                                                               (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                (var (zero {empty} {\ _ -> set})) z1)}
                                                                            {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                          (pair z v)))
                                                                        (\ v1 -> set)))}
                                                                 {\ _ -> set}
                                                                 (var
                                                                  (suc {snoc empty (\ _ -> set)}
                                                                   {\ z ->
                                                                      pi
                                                                      (el
                                                                       (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                        (var (zero {empty} {\ _ -> set})) z))
                                                                      (\ v ->
                                                                         pi
                                                                         (el
                                                                          (eval
                                                                           {snoc (snoc empty (\ _ -> set))
                                                                            (\ g1 ->
                                                                               el
                                                                               (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                (var (zero {empty} {\ _ -> set})) g1))}
                                                                           {\ _ -> set}
                                                                           (var
                                                                            (suc {snoc empty (\ _ -> set)}
                                                                             {\ z1 ->
                                                                                el
                                                                                (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                 (var (zero {empty} {\ _ -> set})) z1)}
                                                                             {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                           (pair z v)))
                                                                         (\ v1 -> set))}
                                                                   {\ g1 -> set} (zero {empty} {\ _ -> set})))
                                                                 g))
                                                               (\ v ->
                                                                  el
                                                                  (eval
                                                                   {snoc
                                                                    (snoc (snoc empty (\ _ -> set))
                                                                     (\ z ->
                                                                        pi
                                                                        (el
                                                                         (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                          (var (zero {empty} {\ _ -> set})) z))
                                                                        (\ v1 ->
                                                                           pi
                                                                           (el
                                                                            (eval
                                                                             {snoc (snoc empty (\ _ -> set))
                                                                              (\ g1 ->
                                                                                 el
                                                                                 (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                  (var (zero {empty} {\ _ -> set})) g1))}
                                                                             {\ _ -> set}
                                                                             (var
                                                                              (suc {snoc empty (\ _ -> set)}
                                                                               {\ z1 ->
                                                                                  el
                                                                                  (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                   (var (zero {empty} {\ _ -> set})) z1)}
                                                                               {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                             (pair z v1)))
                                                                           (\ v2 -> set))))
                                                                    (\ z ->
                                                                       el
                                                                       (eval
                                                                        {snoc (snoc empty (\ _ -> set))
                                                                         (\ z1 ->
                                                                            pi
                                                                            (el
                                                                             (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                              (var (zero {empty} {\ _ -> set})) z1))
                                                                            (\ v1 ->
                                                                               pi
                                                                               (el
                                                                                (eval
                                                                                 {snoc (snoc empty (\ _ -> set))
                                                                                  (\ g1 ->
                                                                                     el
                                                                                     (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                      (var (zero {empty} {\ _ -> set})) g1))}
                                                                                 {\ _ -> set}
                                                                                 (var
                                                                                  (suc {snoc empty (\ _ -> set)}
                                                                                   {\ z2 ->
                                                                                      el
                                                                                      (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                       (var (zero {empty} {\ _ -> set})) z2)}
                                                                                   {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                                 (pair z1 v1)))
                                                                               (\ v2 -> set)))}
                                                                        {\ _ -> set}
                                                                        (var
                                                                         (suc {snoc empty (\ _ -> set)}
                                                                          {\ z1 ->
                                                                             pi
                                                                             (el
                                                                              (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                               (var (zero {empty} {\ _ -> set})) z1))
                                                                             (\ v1 ->
                                                                                pi
                                                                                (el
                                                                                 (eval
                                                                                  {snoc (snoc empty (\ _ -> set))
                                                                                   (\ g1 ->
                                                                                      el
                                                                                      (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                       (var (zero {empty} {\ _ -> set})) g1))}
                                                                                  {\ _ -> set}
                                                                                  (var
                                                                                   (suc {snoc empty (\ _ -> set)}
                                                                                    {\ z2 ->
                                                                                       el
                                                                                       (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                        (var (zero {empty} {\ _ -> set})) z2)}
                                                                                    {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                                  (pair z1 v1)))
                                                                                (\ v2 -> set))}
                                                                          {\ g1 -> set} (zero {empty} {\ _ -> set})))
                                                                        z))}
                                                                   {\ _ -> set}
                                                                   (app
                                                                    {snoc
                                                                     (snoc (snoc empty (\ _ -> set))
                                                                      (\ z ->
                                                                         pi
                                                                         (el
                                                                          (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                           (var (zero {empty} {\ _ -> set})) z))
                                                                         (\ v1 ->
                                                                            pi
                                                                            (el
                                                                             (eval
                                                                              {snoc (snoc empty (\ _ -> set))
                                                                               (\ g1 ->
                                                                                  el
                                                                                  (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                   (var (zero {empty} {\ _ -> set})) g1))}
                                                                              {\ _ -> set}
                                                                              (var
                                                                               (suc {snoc empty (\ _ -> set)}
                                                                                {\ z1 ->
                                                                                   el
                                                                                   (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                    (var (zero {empty} {\ _ -> set})) z1)}
                                                                                {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                              (pair z v1)))
                                                                            (\ v2 -> set))))
                                                                     (\ z ->
                                                                        el
                                                                        (eval
                                                                         {snoc (snoc empty (\ _ -> set))
                                                                          (\ z1 ->
                                                                             pi
                                                                             (el
                                                                              (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                               (var (zero {empty} {\ _ -> set})) z1))
                                                                             (\ v1 ->
                                                                                pi
                                                                                (el
                                                                                 (eval
                                                                                  {snoc (snoc empty (\ _ -> set))
                                                                                   (\ g1 ->
                                                                                      el
                                                                                      (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                       (var (zero {empty} {\ _ -> set})) g1))}
                                                                                  {\ _ -> set}
                                                                                  (var
                                                                                   (suc {snoc empty (\ _ -> set)}
                                                                                    {\ z2 ->
                                                                                       el
                                                                                       (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                        (var (zero {empty} {\ _ -> set})) z2)}
                                                                                    {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                                  (pair z1 v1)))
                                                                                (\ v2 -> set)))}
                                                                         {\ _ -> set}
                                                                         (var
                                                                          (suc {snoc empty (\ _ -> set)}
                                                                           {\ z1 ->
                                                                              pi
                                                                              (el
                                                                               (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                (var (zero {empty} {\ _ -> set})) z1))
                                                                              (\ v1 ->
                                                                                 pi
                                                                                 (el
                                                                                  (eval
                                                                                   {snoc (snoc empty (\ _ -> set))
                                                                                    (\ g1 ->
                                                                                       el
                                                                                       (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                        (var (zero {empty} {\ _ -> set})) g1))}
                                                                                   {\ _ -> set}
                                                                                   (var
                                                                                    (suc {snoc empty (\ _ -> set)}
                                                                                     {\ z2 ->
                                                                                        el
                                                                                        (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                         (var (zero {empty} {\ _ -> set})) z2)}
                                                                                     {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                                   (pair z1 v1)))
                                                                                 (\ v2 -> set))}
                                                                           {\ g1 -> set} (zero {empty} {\ _ -> set})))
                                                                         z))}
                                                                    {\ g1 ->
                                                                       el
                                                                       (eval
                                                                        {snoc (snoc empty (\ _ -> set))
                                                                         (\ z ->
                                                                            pi
                                                                            (el
                                                                             (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                              (var (zero {empty} {\ _ -> set})) z))
                                                                            (\ v1 ->
                                                                               pi
                                                                               (el
                                                                                (eval
                                                                                 {snoc (snoc empty (\ _ -> set))
                                                                                  (\ g2 ->
                                                                                     el
                                                                                     (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                      (var (zero {empty} {\ _ -> set})) g2))}
                                                                                 {\ _ -> set}
                                                                                 (var
                                                                                  (suc {snoc empty (\ _ -> set)}
                                                                                   {\ z1 ->
                                                                                      el
                                                                                      (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                       (var (zero {empty} {\ _ -> set})) z1)}
                                                                                   {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                                 (pair z v1)))
                                                                               (\ v2 -> set)))}
                                                                        {\ _ -> set}
                                                                        (var
                                                                         (suc {snoc empty (\ _ -> set)}
                                                                          {\ z ->
                                                                             pi
                                                                             (el
                                                                              (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                               (var (zero {empty} {\ _ -> set})) z))
                                                                             (\ v1 ->
                                                                                pi
                                                                                (el
                                                                                 (eval
                                                                                  {snoc (snoc empty (\ _ -> set))
                                                                                   (\ g2 ->
                                                                                      el
                                                                                      (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                       (var (zero {empty} {\ _ -> set})) g2))}
                                                                                  {\ _ -> set}
                                                                                  (var
                                                                                   (suc {snoc empty (\ _ -> set)}
                                                                                    {\ z1 ->
                                                                                       el
                                                                                       (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                        (var (zero {empty} {\ _ -> set})) z1)}
                                                                                    {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                                  (pair z v1)))
                                                                                (\ v2 -> set))}
                                                                          {\ g2 -> set} (zero {empty} {\ _ -> set})))
                                                                        (fst g1))}
                                                                    {\ g1 v1 -> set}
                                                                    (app
                                                                     {snoc
                                                                      (snoc (snoc empty (\ _ -> set))
                                                                       (\ z ->
                                                                          pi
                                                                          (el
                                                                           (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                            (var (zero {empty} {\ _ -> set})) z))
                                                                          (\ v1 ->
                                                                             pi
                                                                             (el
                                                                              (eval
                                                                               {snoc (snoc empty (\ _ -> set))
                                                                                (\ g1 ->
                                                                                   el
                                                                                   (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                    (var (zero {empty} {\ _ -> set})) g1))}
                                                                               {\ _ -> set}
                                                                               (var
                                                                                (suc {snoc empty (\ _ -> set)}
                                                                                 {\ z1 ->
                                                                                    el
                                                                                    (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                     (var (zero {empty} {\ _ -> set})) z1)}
                                                                                 {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                               (pair z v1)))
                                                                             (\ v2 -> set))))
                                                                      (\ z ->
                                                                         el
                                                                         (eval
                                                                          {snoc (snoc empty (\ _ -> set))
                                                                           (\ z1 ->
                                                                              pi
                                                                              (el
                                                                               (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                (var (zero {empty} {\ _ -> set})) z1))
                                                                              (\ v1 ->
                                                                                 pi
                                                                                 (el
                                                                                  (eval
                                                                                   {snoc (snoc empty (\ _ -> set))
                                                                                    (\ g1 ->
                                                                                       el
                                                                                       (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                        (var (zero {empty} {\ _ -> set})) g1))}
                                                                                   {\ _ -> set}
                                                                                   (var
                                                                                    (suc {snoc empty (\ _ -> set)}
                                                                                     {\ z2 ->
                                                                                        el
                                                                                        (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                         (var (zero {empty} {\ _ -> set})) z2)}
                                                                                     {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                                   (pair z1 v1)))
                                                                                 (\ v2 -> set)))}
                                                                          {\ _ -> set}
                                                                          (var
                                                                           (suc {snoc empty (\ _ -> set)}
                                                                            {\ z1 ->
                                                                               pi
                                                                               (el
                                                                                (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                 (var (zero {empty} {\ _ -> set})) z1))
                                                                               (\ v1 ->
                                                                                  pi
                                                                                  (el
                                                                                   (eval
                                                                                    {snoc (snoc empty (\ _ -> set))
                                                                                     (\ g1 ->
                                                                                        el
                                                                                        (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                         (var (zero {empty} {\ _ -> set})) g1))}
                                                                                    {\ _ -> set}
                                                                                    (var
                                                                                     (suc {snoc empty (\ _ -> set)}
                                                                                      {\ z2 ->
                                                                                         el
                                                                                         (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                          (var (zero {empty} {\ _ -> set})) z2)}
                                                                                      {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                                    (pair z1 v1)))
                                                                                  (\ v2 -> set))}
                                                                            {\ g1 -> set} (zero {empty} {\ _ -> set})))
                                                                          z))}
                                                                     {\ g1 ->
                                                                        el
                                                                        (eval
                                                                         {snoc (snoc empty (\ _ -> set))
                                                                          (\ z ->
                                                                             pi
                                                                             (el
                                                                              (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                               (var (zero {empty} {\ _ -> set})) z))
                                                                             (\ v1 ->
                                                                                pi
                                                                                (el
                                                                                 (eval
                                                                                  {snoc (snoc empty (\ _ -> set))
                                                                                   (\ g2 ->
                                                                                      el
                                                                                      (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                       (var (zero {empty} {\ _ -> set})) g2))}
                                                                                  {\ _ -> set}
                                                                                  (var
                                                                                   (suc {snoc empty (\ _ -> set)}
                                                                                    {\ z1 ->
                                                                                       el
                                                                                       (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                        (var (zero {empty} {\ _ -> set})) z1)}
                                                                                    {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                                  (pair z v1)))
                                                                                (\ v2 -> set)))}
                                                                         {\ _ -> set}
                                                                         (var
                                                                          (suc {snoc empty (\ _ -> set)}
                                                                           {\ z ->
                                                                              pi
                                                                              (el
                                                                               (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                (var (zero {empty} {\ _ -> set})) z))
                                                                              (\ v1 ->
                                                                                 pi
                                                                                 (el
                                                                                  (eval
                                                                                   {snoc (snoc empty (\ _ -> set))
                                                                                    (\ g2 ->
                                                                                       el
                                                                                       (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                        (var (zero {empty} {\ _ -> set})) g2))}
                                                                                   {\ _ -> set}
                                                                                   (var
                                                                                    (suc {snoc empty (\ _ -> set)}
                                                                                     {\ z1 ->
                                                                                        el
                                                                                        (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                         (var (zero {empty} {\ _ -> set})) z1)}
                                                                                     {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                                   (pair z v1)))
                                                                                 (\ v2 -> set))}
                                                                           {\ g2 -> set} (zero {empty} {\ _ -> set})))
                                                                         (fst g1))}
                                                                     {\ g1 v1 ->
                                                                        pi
                                                                        (el
                                                                         (eval
                                                                          {snoc (snoc empty (\ _ -> set))
                                                                           (\ g2 ->
                                                                              el
                                                                              (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                               (var (zero {empty} {\ _ -> set})) g2))}
                                                                          {\ _ -> set}
                                                                          (var
                                                                           (suc {snoc empty (\ _ -> set)}
                                                                            {\ z ->
                                                                               el
                                                                               (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                (var (zero {empty} {\ _ -> set})) z)}
                                                                            {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                          (pair (fst (fst g1)) v1)))
                                                                        (\ v2 -> set)}
                                                                     (var
                                                                      (suc
                                                                       {snoc (snoc empty (\ _ -> set))
                                                                        (\ z ->
                                                                           pi
                                                                           (el
                                                                            (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                             (var (zero {empty} {\ _ -> set})) z))
                                                                           (\ v1 ->
                                                                              pi
                                                                              (el
                                                                               (eval
                                                                                {snoc (snoc empty (\ _ -> set))
                                                                                 (\ g1 ->
                                                                                    el
                                                                                    (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                     (var (zero {empty} {\ _ -> set})) g1))}
                                                                                {\ _ -> set}
                                                                                (var
                                                                                 (suc {snoc empty (\ _ -> set)}
                                                                                  {\ z1 ->
                                                                                     el
                                                                                     (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                      (var (zero {empty} {\ _ -> set})) z1)}
                                                                                  {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                                (pair z v1)))
                                                                              (\ v2 -> set)))}
                                                                       {\ z ->
                                                                          el
                                                                          (eval
                                                                           {snoc (snoc empty (\ _ -> set))
                                                                            (\ z1 ->
                                                                               pi
                                                                               (el
                                                                                (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                 (var (zero {empty} {\ _ -> set})) z1))
                                                                               (\ v1 ->
                                                                                  pi
                                                                                  (el
                                                                                   (eval
                                                                                    {snoc (snoc empty (\ _ -> set))
                                                                                     (\ g1 ->
                                                                                        el
                                                                                        (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                         (var (zero {empty} {\ _ -> set})) g1))}
                                                                                    {\ _ -> set}
                                                                                    (var
                                                                                     (suc {snoc empty (\ _ -> set)}
                                                                                      {\ z2 ->
                                                                                         el
                                                                                         (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                          (var (zero {empty} {\ _ -> set})) z2)}
                                                                                      {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                                    (pair z1 v1)))
                                                                                  (\ v2 -> set)))}
                                                                           {\ _ -> set}
                                                                           (var
                                                                            (suc {snoc empty (\ _ -> set)}
                                                                             {\ z1 ->
                                                                                pi
                                                                                (el
                                                                                 (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                  (var (zero {empty} {\ _ -> set})) z1))
                                                                                (\ v1 ->
                                                                                   pi
                                                                                   (el
                                                                                    (eval
                                                                                     {snoc (snoc empty (\ _ -> set))
                                                                                      (\ g1 ->
                                                                                         el
                                                                                         (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                          (var (zero {empty} {\ _ -> set})) g1))}
                                                                                     {\ _ -> set}
                                                                                     (var
                                                                                      (suc {snoc empty (\ _ -> set)}
                                                                                       {\ z2 ->
                                                                                          el
                                                                                          (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                           (var (zero {empty} {\ _ -> set})) z2)}
                                                                                       {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                                     (pair z1 v1)))
                                                                                   (\ v2 -> set))}
                                                                             {\ g1 -> set} (zero {empty} {\ _ -> set})))
                                                                           z)}
                                                                       {\ g1 ->
                                                                          pi
                                                                          (el
                                                                           (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                            (var (zero {empty} {\ _ -> set})) (fst g1)))
                                                                          (\ v1 ->
                                                                             pi
                                                                             (el
                                                                              (eval
                                                                               {snoc (snoc empty (\ _ -> set))
                                                                                (\ g2 ->
                                                                                   el
                                                                                   (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                    (var (zero {empty} {\ _ -> set})) g2))}
                                                                               {\ _ -> set}
                                                                               (var
                                                                                (suc {snoc empty (\ _ -> set)}
                                                                                 {\ z ->
                                                                                    el
                                                                                    (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                     (var (zero {empty} {\ _ -> set})) z)}
                                                                                 {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                               (pair (fst g1) v1)))
                                                                             (\ v2 -> set))}
                                                                       (zero {snoc empty (\ _ -> set)}
                                                                        {\ z ->
                                                                           pi
                                                                           (el
                                                                            (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                             (var (zero {empty} {\ _ -> set})) z))
                                                                           (\ v1 ->
                                                                              pi
                                                                              (el
                                                                               (eval
                                                                                {snoc (snoc empty (\ _ -> set))
                                                                                 (\ g1 ->
                                                                                    el
                                                                                    (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                     (var (zero {empty} {\ _ -> set})) g1))}
                                                                                {\ _ -> set}
                                                                                (var
                                                                                 (suc {snoc empty (\ _ -> set)}
                                                                                  {\ z1 ->
                                                                                     el
                                                                                     (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                      (var (zero {empty} {\ _ -> set})) z1)}
                                                                                  {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                                (pair z v1)))
                                                                              (\ v2 -> set))})))
                                                                     (var
                                                                      (zero
                                                                       {snoc (snoc empty (\ v1 -> set))
                                                                        (\ z ->
                                                                           pi
                                                                           (el
                                                                            (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                             (var (zero {empty} {\ _ -> set})) z))
                                                                           (\ v1 ->
                                                                              pi
                                                                              (el
                                                                               (eval
                                                                                {snoc (snoc empty (\ _ -> set))
                                                                                 (\ g1 ->
                                                                                    el
                                                                                    (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                     (var (zero {empty} {\ _ -> set})) g1))}
                                                                                {\ _ -> set}
                                                                                (var
                                                                                 (suc {snoc empty (\ _ -> set)}
                                                                                  {\ z1 ->
                                                                                     el
                                                                                     (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                      (var (zero {empty} {\ _ -> set})) z1)}
                                                                                  {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                                (pair z v1)))
                                                                              (\ v2 -> set)))}
                                                                       {\ z ->
                                                                          el
                                                                          (eval
                                                                           {snoc (snoc empty (\ _ -> set))
                                                                            (\ z1 ->
                                                                               pi
                                                                               (el
                                                                                (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                 (var (zero {empty} {\ _ -> set})) z1))
                                                                               (\ v1 ->
                                                                                  pi
                                                                                  (el
                                                                                   (eval
                                                                                    {snoc (snoc empty (\ _ -> set))
                                                                                     (\ g1 ->
                                                                                        el
                                                                                        (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                         (var (zero {empty} {\ _ -> set})) g1))}
                                                                                    {\ _ -> set}
                                                                                    (var
                                                                                     (suc {snoc empty (\ _ -> set)}
                                                                                      {\ z2 ->
                                                                                         el
                                                                                         (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                          (var (zero {empty} {\ _ -> set})) z2)}
                                                                                      {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                                    (pair z1 v1)))
                                                                                  (\ v2 -> set)))}
                                                                           {\ _ -> set}
                                                                           (var
                                                                            (suc {snoc empty (\ _ -> set)}
                                                                             {\ z1 ->
                                                                                pi
                                                                                (el
                                                                                 (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                  (var (zero {empty} {\ _ -> set})) z1))
                                                                                (\ v1 ->
                                                                                   pi
                                                                                   (el
                                                                                    (eval
                                                                                     {snoc (snoc empty (\ _ -> set))
                                                                                      (\ g1 ->
                                                                                         el
                                                                                         (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                          (var (zero {empty} {\ _ -> set})) g1))}
                                                                                     {\ _ -> set}
                                                                                     (var
                                                                                      (suc {snoc empty (\ _ -> set)}
                                                                                       {\ z2 ->
                                                                                          el
                                                                                          (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                           (var (zero {empty} {\ _ -> set})) z2)}
                                                                                       {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                                     (pair z1 v1)))
                                                                                   (\ v2 -> set))}
                                                                             {\ g1 -> set} (zero {empty} {\ _ -> set})))
                                                                           z)})))
                                                                    (var
                                                                     (zero
                                                                      {snoc (snoc empty (\ v1 -> set))
                                                                       (\ z ->
                                                                          pi
                                                                          (el
                                                                           (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                            (var (zero {empty} {\ _ -> set})) z))
                                                                          (\ v1 ->
                                                                             pi
                                                                             (el
                                                                              (eval
                                                                               {snoc (snoc empty (\ _ -> set))
                                                                                (\ g1 ->
                                                                                   el
                                                                                   (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                    (var (zero {empty} {\ _ -> set})) g1))}
                                                                               {\ _ -> set}
                                                                               (var
                                                                                (suc {snoc empty (\ _ -> set)}
                                                                                 {\ z1 ->
                                                                                    el
                                                                                    (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                     (var (zero {empty} {\ _ -> set})) z1)}
                                                                                 {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                               (pair z v1)))
                                                                             (\ v2 -> set)))}
                                                                      {\ z ->
                                                                         el
                                                                         (eval
                                                                          {snoc (snoc empty (\ _ -> set))
                                                                           (\ z1 ->
                                                                              pi
                                                                              (el
                                                                               (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                (var (zero {empty} {\ _ -> set})) z1))
                                                                              (\ v1 ->
                                                                                 pi
                                                                                 (el
                                                                                  (eval
                                                                                   {snoc (snoc empty (\ _ -> set))
                                                                                    (\ g1 ->
                                                                                       el
                                                                                       (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                        (var (zero {empty} {\ _ -> set})) g1))}
                                                                                   {\ _ -> set}
                                                                                   (var
                                                                                    (suc {snoc empty (\ _ -> set)}
                                                                                     {\ z2 ->
                                                                                        el
                                                                                        (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                         (var (zero {empty} {\ _ -> set})) z2)}
                                                                                     {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                                   (pair z1 v1)))
                                                                                 (\ v2 -> set)))}
                                                                          {\ _ -> set}
                                                                          (var
                                                                           (suc {snoc empty (\ _ -> set)}
                                                                            {\ z1 ->
                                                                               pi
                                                                               (el
                                                                                (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                 (var (zero {empty} {\ _ -> set})) z1))
                                                                               (\ v1 ->
                                                                                  pi
                                                                                  (el
                                                                                   (eval
                                                                                    {snoc (snoc empty (\ _ -> set))
                                                                                     (\ g1 ->
                                                                                        el
                                                                                        (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                         (var (zero {empty} {\ _ -> set})) g1))}
                                                                                    {\ _ -> set}
                                                                                    (var
                                                                                     (suc {snoc empty (\ _ -> set)}
                                                                                      {\ z2 ->
                                                                                         el
                                                                                         (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                          (var (zero {empty} {\ _ -> set})) z2)}
                                                                                      {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                                    (pair z1 v1)))
                                                                                  (\ v2 -> set))}
                                                                            {\ g1 -> set} (zero {empty} {\ _ -> set})))
                                                                          z)})))
                                                                   (pair g v)))} (pi' (el' (var (zero {empty} {\_ -> set})))

    (pi' {snoc (snoc empty (\_ -> set)) (\x -> _)} {\x -> _} {\_ -> set}
      (el' {snoc (snoc empty (\_ -> set)) (\g -> el
                                                   (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                    (var (zero {empty} {\ _ -> set})) g))} (var (suc {snoc empty (\_ -> set)} {\z -> ?} {\_ -> set} (zero {empty} {\_ -> set})))) set'))
     -- Identity.
  (pi' {snoc (snoc empty (\ z -> set))
          (\ z ->
             pi
             (el
              (eval {snoc empty (\ _ -> set)} {\ _ -> set}
               (var (zero {empty} {\ _ -> set})) z))
             (\ v ->
                pi
                (el
                 (eval
                  {snoc (snoc empty (\ _ -> set))
                   (\ g1 ->
                      el
                      (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                       (var (zero {empty} {\ _ -> set})) g1))}
                  {\ _ -> set}
                  (var
                   (suc {snoc empty (\ _ -> set)}
                    {\ z1 ->
                       el
                       (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                        (var (zero {empty} {\ _ -> set})) z1)}
                    {\ _ -> set} (zero {empty} {\ _ -> set})))
                  (pair z v)))
                (\ v1 -> set)))} {\ g ->
                                     el
                                     (eval
                                      {snoc (snoc empty (\ z -> set))
                                       (\ z ->
                                          pi
                                          (el
                                           (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                            (var (zero {empty} {\ _ -> set})) z))
                                          (\ v ->
                                             pi
                                             (el
                                              (eval
                                               {snoc (snoc empty (\ _ -> set))
                                                (\ g1 ->
                                                   el
                                                   (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                    (var (zero {empty} {\ _ -> set})) g1))}
                                               {\ _ -> set}
                                               (var
                                                (suc {snoc empty (\ _ -> set)}
                                                 {\ z1 ->
                                                    el
                                                    (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                     (var (zero {empty} {\ _ -> set})) z1)}
                                                 {\ _ -> set} (zero {empty} {\ _ -> set})))
                                               (pair z v)))
                                             (\ v1 -> set)))}
                                      {\ _ -> set}
                                      (var
                                       (suc {snoc empty (\ _ -> set)}
                                        {\ z ->
                                           pi
                                           (el
                                            (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                             (var (zero {empty} {\ _ -> set})) z))
                                           (\ v ->
                                              pi
                                              (el
                                               (eval
                                                {snoc (snoc empty (\ _ -> set))
                                                 (\ g1 ->
                                                    el
                                                    (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                     (var (zero {empty} {\ _ -> set})) g1))}
                                                {\ _ -> set}
                                                (var
                                                 (suc {snoc empty (\ _ -> set)}
                                                  {\ z1 ->
                                                     el
                                                     (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                      (var (zero {empty} {\ _ -> set})) z1)}
                                                  {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                (pair z v)))
                                              (\ v1 -> set))}
                                        {\ g1 -> set} (zero {empty} {\ _ -> set})))
                                      g)} {\ g ->
                                               el
                                               (eval
                                                {snoc
                                                 (snoc (snoc empty (\ _ -> set))
                                                  (\ z ->
                                                     pi
                                                     (el
                                                      (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                       (var (zero {empty} {\ _ -> set})) z))
                                                     (\ v ->
                                                        pi
                                                        (el
                                                         (eval
                                                          {snoc (snoc empty (\ _ -> set))
                                                           (\ g1 ->
                                                              el
                                                              (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                               (var (zero {empty} {\ _ -> set})) g1))}
                                                          {\ _ -> set}
                                                          (var
                                                           (suc {snoc empty (\ _ -> set)}
                                                            {\ z1 ->
                                                               el
                                                               (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                (var (zero {empty} {\ _ -> set})) z1)}
                                                            {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                          (pair z v)))
                                                        (\ v1 -> set))))
                                                 (\ z ->
                                                    el
                                                    (eval
                                                     {snoc (snoc empty (\ _ -> set))
                                                      (\ z1 ->
                                                         pi
                                                         (el
                                                          (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                           (var (zero {empty} {\ _ -> set})) z1))
                                                         (\ v ->
                                                            pi
                                                            (el
                                                             (eval
                                                              {snoc (snoc empty (\ _ -> set))
                                                               (\ g1 ->
                                                                  el
                                                                  (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                   (var (zero {empty} {\ _ -> set})) g1))}
                                                              {\ _ -> set}
                                                              (var
                                                               (suc {snoc empty (\ _ -> set)}
                                                                {\ z2 ->
                                                                   el
                                                                   (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                    (var (zero {empty} {\ _ -> set})) z2)}
                                                                {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                              (pair z1 v)))
                                                            (\ v1 -> set)))}
                                                     {\ _ -> set}
                                                     (var
                                                      (suc {snoc empty (\ _ -> set)}
                                                       {\ z1 ->
                                                          pi
                                                          (el
                                                           (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                            (var (zero {empty} {\ _ -> set})) z1))
                                                          (\ v ->
                                                             pi
                                                             (el
                                                              (eval
                                                               {snoc (snoc empty (\ _ -> set))
                                                                (\ g1 ->
                                                                   el
                                                                   (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                    (var (zero {empty} {\ _ -> set})) g1))}
                                                               {\ _ -> set}
                                                               (var
                                                                (suc {snoc empty (\ _ -> set)}
                                                                 {\ z2 ->
                                                                    el
                                                                    (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                     (var (zero {empty} {\ _ -> set})) z2)}
                                                                 {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                               (pair z1 v)))
                                                             (\ v1 -> set))}
                                                       {\ g1 -> set} (zero {empty} {\ _ -> set})))
                                                     z))}
                                                {\ _ -> set}
                                                (app
                                                 {snoc
                                                  (snoc (snoc empty (\ _ -> set))
                                                   (\ z ->
                                                      pi
                                                      (el
                                                       (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                        (var (zero {empty} {\ _ -> set})) z))
                                                      (\ v ->
                                                         pi
                                                         (el
                                                          (eval
                                                           {snoc (snoc empty (\ _ -> set))
                                                            (\ g1 ->
                                                               el
                                                               (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                (var (zero {empty} {\ _ -> set})) g1))}
                                                           {\ _ -> set}
                                                           (var
                                                            (suc {snoc empty (\ _ -> set)}
                                                             {\ z1 ->
                                                                el
                                                                (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                 (var (zero {empty} {\ _ -> set})) z1)}
                                                             {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                           (pair z v)))
                                                         (\ v1 -> set))))
                                                  (\ z ->
                                                     el
                                                     (eval
                                                      {snoc (snoc empty (\ _ -> set))
                                                       (\ z1 ->
                                                          pi
                                                          (el
                                                           (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                            (var (zero {empty} {\ _ -> set})) z1))
                                                          (\ v ->
                                                             pi
                                                             (el
                                                              (eval
                                                               {snoc (snoc empty (\ _ -> set))
                                                                (\ g1 ->
                                                                   el
                                                                   (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                    (var (zero {empty} {\ _ -> set})) g1))}
                                                               {\ _ -> set}
                                                               (var
                                                                (suc {snoc empty (\ _ -> set)}
                                                                 {\ z2 ->
                                                                    el
                                                                    (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                     (var (zero {empty} {\ _ -> set})) z2)}
                                                                 {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                               (pair z1 v)))
                                                             (\ v1 -> set)))}
                                                      {\ _ -> set}
                                                      (var
                                                       (suc {snoc empty (\ _ -> set)}
                                                        {\ z1 ->
                                                           pi
                                                           (el
                                                            (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                             (var (zero {empty} {\ _ -> set})) z1))
                                                           (\ v ->
                                                              pi
                                                              (el
                                                               (eval
                                                                {snoc (snoc empty (\ _ -> set))
                                                                 (\ g1 ->
                                                                    el
                                                                    (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                     (var (zero {empty} {\ _ -> set})) g1))}
                                                                {\ _ -> set}
                                                                (var
                                                                 (suc {snoc empty (\ _ -> set)}
                                                                  {\ z2 ->
                                                                     el
                                                                     (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                      (var (zero {empty} {\ _ -> set})) z2)}
                                                                  {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                (pair z1 v)))
                                                              (\ v1 -> set))}
                                                        {\ g1 -> set} (zero {empty} {\ _ -> set})))
                                                      z))}
                                                 {\ g1 ->
                                                    el
                                                    (eval
                                                     {snoc (snoc empty (\ _ -> set))
                                                      (\ z ->
                                                         pi
                                                         (el
                                                          (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                           (var (zero {empty} {\ _ -> set})) z))
                                                         (\ v ->
                                                            pi
                                                            (el
                                                             (eval
                                                              {snoc (snoc empty (\ _ -> set))
                                                               (\ g1 ->
                                                                  el
                                                                  (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                   (var (zero {empty} {\ _ -> set})) g1))}
                                                              {\ _ -> set}
                                                              (var
                                                               (suc {snoc empty (\ _ -> set)}
                                                                {\ z1 ->
                                                                   el
                                                                   (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                    (var (zero {empty} {\ _ -> set})) z1)}
                                                                {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                              (pair z v)))
                                                            (\ v1 -> set)))}
                                                     {\ _ -> set}
                                                     (var
                                                      (suc {snoc empty (\ _ -> set)}
                                                       {\ z ->
                                                          pi
                                                          (el
                                                           (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                            (var (zero {empty} {\ _ -> set})) z))
                                                          (\ v ->
                                                             pi
                                                             (el
                                                              (eval
                                                               {snoc (snoc empty (\ _ -> set))
                                                                (\ g1 ->
                                                                   el
                                                                   (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                    (var (zero {empty} {\ _ -> set})) g1))}
                                                               {\ _ -> set}
                                                               (var
                                                                (suc {snoc empty (\ _ -> set)}
                                                                 {\ z1 ->
                                                                    el
                                                                    (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                     (var (zero {empty} {\ _ -> set})) z1)}
                                                                 {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                               (pair z v)))
                                                             (\ v1 -> set))}
                                                       {\ g2 -> set} (zero {empty} {\ _ -> set})))
                                                     (fst g1))}
                                                 {\ g1 v1 -> set}
                                                 (app
                                                  {snoc
                                                   (snoc (snoc empty (\ _ -> set))
                                                    (\ z ->
                                                       pi
                                                       (el
                                                        (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                         (var (zero {empty} {\ _ -> set})) z))
                                                       (\ v ->
                                                          pi
                                                          (el
                                                           (eval
                                                            {snoc (snoc empty (\ _ -> set))
                                                             (\ g1 ->
                                                                el
                                                                (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                 (var (zero {empty} {\ _ -> set})) g1))}
                                                            {\ _ -> set}
                                                            (var
                                                             (suc {snoc empty (\ _ -> set)}
                                                              {\ z1 ->
                                                                 el
                                                                 (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                  (var (zero {empty} {\ _ -> set})) z1)}
                                                              {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                            (pair z v)))
                                                          (\ v1 -> set))))
                                                   (\ z ->
                                                      el
                                                      (eval
                                                       {snoc (snoc empty (\ _ -> set))
                                                        (\ z1 ->
                                                           pi
                                                           (el
                                                            (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                             (var (zero {empty} {\ _ -> set})) z1))
                                                           (\ v ->
                                                              pi
                                                              (el
                                                               (eval
                                                                {snoc (snoc empty (\ _ -> set))
                                                                 (\ g1 ->
                                                                    el
                                                                    (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                     (var (zero {empty} {\ _ -> set})) g1))}
                                                                {\ _ -> set}
                                                                (var
                                                                 (suc {snoc empty (\ _ -> set)}
                                                                  {\ z2 ->
                                                                     el
                                                                     (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                      (var (zero {empty} {\ _ -> set})) z2)}
                                                                  {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                (pair z1 v)))
                                                              (\ v1 -> set)))}
                                                       {\ _ -> set}
                                                       (var
                                                        (suc {snoc empty (\ _ -> set)}
                                                         {\ z1 ->
                                                            pi
                                                            (el
                                                             (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                              (var (zero {empty} {\ _ -> set})) z1))
                                                            (\ v ->
                                                               pi
                                                               (el
                                                                (eval
                                                                 {snoc (snoc empty (\ _ -> set))
                                                                  (\ g1 ->
                                                                     el
                                                                     (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                      (var (zero {empty} {\ _ -> set})) g1))}
                                                                 {\ _ -> set}
                                                                 (var
                                                                  (suc {snoc empty (\ _ -> set)}
                                                                   {\ z2 ->
                                                                      el
                                                                      (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                       (var (zero {empty} {\ _ -> set})) z2)}
                                                                   {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                 (pair z1 v)))
                                                               (\ v1 -> set))}
                                                         {\ g1 -> set} (zero {empty} {\ _ -> set})))
                                                       z))}
                                                  {\ g1 ->
                                                     el
                                                     (eval
                                                      {snoc (snoc empty (\ _ -> set))
                                                       (\ z ->
                                                          pi
                                                          (el
                                                           (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                            (var (zero {empty} {\ _ -> set})) z))
                                                          (\ v ->
                                                             pi
                                                             (el
                                                              (eval
                                                               {snoc (snoc empty (\ _ -> set))
                                                                (\ g1 ->
                                                                   el
                                                                   (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                    (var (zero {empty} {\ _ -> set})) g1))}
                                                               {\ _ -> set}
                                                               (var
                                                                (suc {snoc empty (\ _ -> set)}
                                                                 {\ z1 ->
                                                                    el
                                                                    (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                     (var (zero {empty} {\ _ -> set})) z1)}
                                                                 {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                               (pair z v)))
                                                             (\ v1 -> set)))}
                                                      {\ _ -> set}
                                                      (var
                                                       (suc {snoc empty (\ _ -> set)}
                                                        {\ z ->
                                                           pi
                                                           (el
                                                            (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                             (var (zero {empty} {\ _ -> set})) z))
                                                           (\ v ->
                                                              pi
                                                              (el
                                                               (eval
                                                                {snoc (snoc empty (\ _ -> set))
                                                                 (\ g1 ->
                                                                    el
                                                                    (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                     (var (zero {empty} {\ _ -> set})) g1))}
                                                                {\ _ -> set}
                                                                (var
                                                                 (suc {snoc empty (\ _ -> set)}
                                                                  {\ z1 ->
                                                                     el
                                                                     (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                      (var (zero {empty} {\ _ -> set})) z1)}
                                                                  {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                (pair z v)))
                                                              (\ v1 -> set))}
                                                        {\ g2 -> set} (zero {empty} {\ _ -> set})))
                                                      (fst g1))}
                                                  {\ g1 v ->
                                                     pi
                                                     (el
                                                      (eval
                                                       {snoc (snoc empty (\ _ -> set))
                                                        (\ g1 ->
                                                           el
                                                           (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                            (var (zero {empty} {\ _ -> set})) g1))}
                                                       {\ _ -> set}
                                                       (var
                                                        (suc {snoc empty (\ _ -> set)}
                                                         {\ z ->
                                                            el
                                                            (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                             (var (zero {empty} {\ _ -> set})) z)}
                                                         {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                       (pair (fst (fst g1)) v)))
                                                     (\ v1 -> set)}
                                                  (var
                                                   (suc
                                                    {snoc (snoc empty (\ _ -> set))
                                                     (\ z ->
                                                        pi
                                                        (el
                                                         (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                          (var (zero {empty} {\ _ -> set})) z))
                                                        (\ v ->
                                                           pi
                                                           (el
                                                            (eval
                                                             {snoc (snoc empty (\ _ -> set))
                                                              (\ g1 ->
                                                                 el
                                                                 (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                  (var (zero {empty} {\ _ -> set})) g1))}
                                                             {\ _ -> set}
                                                             (var
                                                              (suc {snoc empty (\ _ -> set)}
                                                               {\ z1 ->
                                                                  el
                                                                  (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                   (var (zero {empty} {\ _ -> set})) z1)}
                                                               {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                             (pair z v)))
                                                           (\ v1 -> set)))}
                                                    {\ z ->
                                                       el
                                                       (eval
                                                        {snoc (snoc empty (\ _ -> set))
                                                         (\ z1 ->
                                                            pi
                                                            (el
                                                             (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                              (var (zero {empty} {\ _ -> set})) z1))
                                                            (\ v ->
                                                               pi
                                                               (el
                                                                (eval
                                                                 {snoc (snoc empty (\ _ -> set))
                                                                  (\ g1 ->
                                                                     el
                                                                     (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                      (var (zero {empty} {\ _ -> set})) g1))}
                                                                 {\ _ -> set}
                                                                 (var
                                                                  (suc {snoc empty (\ _ -> set)}
                                                                   {\ z2 ->
                                                                      el
                                                                      (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                       (var (zero {empty} {\ _ -> set})) z2)}
                                                                   {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                 (pair z1 v)))
                                                               (\ v1 -> set)))}
                                                        {\ _ -> set}
                                                        (var
                                                         (suc {snoc empty (\ _ -> set)}
                                                          {\ z1 ->
                                                             pi
                                                             (el
                                                              (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                               (var (zero {empty} {\ _ -> set})) z1))
                                                             (\ v ->
                                                                pi
                                                                (el
                                                                 (eval
                                                                  {snoc (snoc empty (\ _ -> set))
                                                                   (\ g1 ->
                                                                      el
                                                                      (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                       (var (zero {empty} {\ _ -> set})) g1))}
                                                                  {\ _ -> set}
                                                                  (var
                                                                   (suc {snoc empty (\ _ -> set)}
                                                                    {\ z2 ->
                                                                       el
                                                                       (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                        (var (zero {empty} {\ _ -> set})) z2)}
                                                                    {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                  (pair z1 v)))
                                                                (\ v1 -> set))}
                                                          {\ g1 -> set} (zero {empty} {\ _ -> set})))
                                                        z)}
                                                    {\ g1 ->
                                                       pi
                                                       (el
                                                        (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                         (var (zero {empty} {\ _ -> set})) (fst g1)))
                                                       (\ v ->
                                                          pi
                                                          (el
                                                           (eval
                                                            {snoc (snoc empty (\ _ -> set))
                                                             (\ g1 ->
                                                                el
                                                                (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                 (var (zero {empty} {\ _ -> set})) g1))}
                                                            {\ _ -> set}
                                                            (var
                                                             (suc {snoc empty (\ _ -> set)}
                                                              {\ z ->
                                                                 el
                                                                 (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                  (var (zero {empty} {\ _ -> set})) z)}
                                                              {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                            (pair (fst g1) v)))
                                                          (\ v1 -> set))}
                                                    (zero {snoc empty (\ _ -> set)}
                                                     {\ z ->
                                                        pi
                                                        (el
                                                         (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                          (var (zero {empty} {\ _ -> set})) z))
                                                        (\ v ->
                                                           pi
                                                           (el
                                                            (eval
                                                             {snoc (snoc empty (\ _ -> set))
                                                              (\ g1 ->
                                                                 el
                                                                 (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                  (var (zero {empty} {\ _ -> set})) g1))}
                                                             {\ _ -> set}
                                                             (var
                                                              (suc {snoc empty (\ _ -> set)}
                                                               {\ z1 ->
                                                                  el
                                                                  (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                   (var (zero {empty} {\ _ -> set})) z1)}
                                                               {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                             (pair z v)))
                                                           (\ v1 -> set))})))
                                                  (var
                                                   (zero
                                                    {snoc (snoc empty (\ v -> set))
                                                     (\ z ->
                                                        pi
                                                        (el
                                                         (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                          (var (zero {empty} {\ _ -> set})) z))
                                                        (\ v ->
                                                           pi
                                                           (el
                                                            (eval
                                                             {snoc (snoc empty (\ _ -> set))
                                                              (\ g1 ->
                                                                 el
                                                                 (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                  (var (zero {empty} {\ _ -> set})) g1))}
                                                             {\ _ -> set}
                                                             (var
                                                              (suc {snoc empty (\ _ -> set)}
                                                               {\ z1 ->
                                                                  el
                                                                  (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                   (var (zero {empty} {\ _ -> set})) z1)}
                                                               {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                             (pair z v)))
                                                           (\ v1 -> set)))}
                                                    {\ z ->
                                                       el
                                                       (eval
                                                        {snoc (snoc empty (\ _ -> set))
                                                         (\ z1 ->
                                                            pi
                                                            (el
                                                             (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                              (var (zero {empty} {\ _ -> set})) z1))
                                                            (\ v ->
                                                               pi
                                                               (el
                                                                (eval
                                                                 {snoc (snoc empty (\ _ -> set))
                                                                  (\ g1 ->
                                                                     el
                                                                     (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                      (var (zero {empty} {\ _ -> set})) g1))}
                                                                 {\ _ -> set}
                                                                 (var
                                                                  (suc {snoc empty (\ _ -> set)}
                                                                   {\ z2 ->
                                                                      el
                                                                      (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                       (var (zero {empty} {\ _ -> set})) z2)}
                                                                   {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                 (pair z1 v)))
                                                               (\ v1 -> set)))}
                                                        {\ _ -> set}
                                                        (var
                                                         (suc {snoc empty (\ _ -> set)}
                                                          {\ z1 ->
                                                             pi
                                                             (el
                                                              (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                               (var (zero {empty} {\ _ -> set})) z1))
                                                             (\ v ->
                                                                pi
                                                                (el
                                                                 (eval
                                                                  {snoc (snoc empty (\ _ -> set))
                                                                   (\ g1 ->
                                                                      el
                                                                      (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                       (var (zero {empty} {\ _ -> set})) g1))}
                                                                  {\ _ -> set}
                                                                  (var
                                                                   (suc {snoc empty (\ _ -> set)}
                                                                    {\ z2 ->
                                                                       el
                                                                       (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                        (var (zero {empty} {\ _ -> set})) z2)}
                                                                    {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                  (pair z1 v)))
                                                                (\ v1 -> set))}
                                                          {\ g1 -> set} (zero {empty} {\ _ -> set})))
                                                        z)})))
                                                 (var
                                                  (zero
                                                   {snoc (snoc empty (\ v -> set))
                                                    (\ z ->
                                                       pi
                                                       (el
                                                        (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                         (var (zero {empty} {\ _ -> set})) z))
                                                       (\ v ->
                                                          pi
                                                          (el
                                                           (eval
                                                            {snoc (snoc empty (\ _ -> set))
                                                             (\ g1 ->
                                                                el
                                                                (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                 (var (zero {empty} {\ _ -> set})) g1))}
                                                            {\ _ -> set}
                                                            (var
                                                             (suc {snoc empty (\ _ -> set)}
                                                              {\ z1 ->
                                                                 el
                                                                 (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                  (var (zero {empty} {\ _ -> set})) z1)}
                                                              {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                            (pair z v)))
                                                          (\ v1 -> set)))}
                                                   {\ z ->
                                                      el
                                                      (eval
                                                       {snoc (snoc empty (\ _ -> set))
                                                        (\ z1 ->
                                                           pi
                                                           (el
                                                            (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                             (var (zero {empty} {\ _ -> set})) z1))
                                                           (\ v ->
                                                              pi
                                                              (el
                                                               (eval
                                                                {snoc (snoc empty (\ _ -> set))
                                                                 (\ g1 ->
                                                                    el
                                                                    (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                     (var (zero {empty} {\ _ -> set})) g1))}
                                                                {\ _ -> set}
                                                                (var
                                                                 (suc {snoc empty (\ _ -> set)}
                                                                  {\ z2 ->
                                                                     el
                                                                     (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                      (var (zero {empty} {\ _ -> set})) z2)}
                                                                  {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                (pair z1 v)))
                                                              (\ v1 -> set)))}
                                                       {\ _ -> set}
                                                       (var
                                                        (suc {snoc empty (\ _ -> set)}
                                                         {\ z1 ->
                                                            pi
                                                            (el
                                                             (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                              (var (zero {empty} {\ _ -> set})) z1))
                                                            (\ v ->
                                                               pi
                                                               (el
                                                                (eval
                                                                 {snoc (snoc empty (\ _ -> set))
                                                                  (\ g1 ->
                                                                     el
                                                                     (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                      (var (zero {empty} {\ _ -> set})) g1))}
                                                                 {\ _ -> set}
                                                                 (var
                                                                  (suc {snoc empty (\ _ -> set)}
                                                                   {\ z2 ->
                                                                      el
                                                                      (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                       (var (zero {empty} {\ _ -> set})) z2)}
                                                                   {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                 (pair z1 v)))
                                                               (\ v1 -> set))}
                                                         {\ g1 -> set} (zero {empty} {\ _ -> set})))
                                                       z)})))
                                                g)} (el' {snoc (snoc empty (\ z -> set))
                                                            (\ z ->
                                                               pi
                                                               (el
                                                                (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                 (var (zero {empty} {\ _ -> set})) z))
                                                               (\ v ->
                                                                  pi
                                                                  (el
                                                                   (eval
                                                                    {snoc (snoc empty (\ _ -> set))
                                                                     (\ g1 ->
                                                                        el
                                                                        (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                         (var (zero {empty} {\ _ -> set})) g1))}
                                                                    {\ _ -> set}
                                                                    (var
                                                                     (suc {snoc empty (\ _ -> set)}
                                                                      {\ z1 ->
                                                                         el
                                                                         (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                          (var (zero {empty} {\ _ -> set})) z1)}
                                                                      {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                    (pair z v)))
                                                                  (\ v1 -> set)))}
      (var (suc {snoc empty (\ z -> set)} {\ z ->
                                                                                                                          pi
                                                                                                                          (el
                                                                                                                           (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                                                            (var (zero {empty} {\ _ -> set})) z))
                                                                                                                          (\ v ->
                                                                                                                             pi
                                                                                                                             (el
                                                                                                                              (eval
                                                                                                                               {snoc (snoc empty (\ _ -> set))
                                                                                                                                (\ g1 ->
                                                                                                                                   el
                                                                                                                                   (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                                                                    (var (zero {empty} {\ _ -> set})) g1))}
                                                                                                                               {\ _ -> set}
                                                                                                                               (var
                                                                                                                                (suc {snoc empty (\ _ -> set)}
                                                                                                                                 {\ z1 ->
                                                                                                                                    el
                                                                                                                                    (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                                                                     (var (zero {empty} {\ _ -> set})) z1)}
                                                                                                                                 {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                                                                               (pair z v)))
                                                                                                                             (\ v1 -> set))} {\ g -> set} (zero {empty} {\ _ -> set}))))
       (el' {snoc
               (snoc (snoc empty (\ z -> set))
                (\ z ->
                   pi
                   (el
                    (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                     (var (zero {empty} {\ _ -> set})) z))
                   (\ v ->
                      pi
                      (el
                       (eval
                        {snoc (snoc empty (\ _ -> set))
                         (\ g1 ->
                            el
                            (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                             (var (zero {empty} {\ _ -> set})) g1))}
                        {\ _ -> set}
                        (var
                         (suc {snoc empty (\ _ -> set)}
                          {\ z1 ->
                             el
                             (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                              (var (zero {empty} {\ _ -> set})) z1)}
                          {\ _ -> set} (zero {empty} {\ _ -> set})))
                        (pair z v)))
                      (\ v1 -> set))))
               (\ z ->
                  el
                  (eval
                   {snoc (snoc empty (\ z1 -> set))
                    (\ z1 ->
                       pi
                       (el
                        (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                         (var (zero {empty} {\ _ -> set})) z1))
                       (\ v ->
                          pi
                          (el
                           (eval
                            {snoc (snoc empty (\ _ -> set))
                             (\ g1 ->
                                el
                                (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                 (var (zero {empty} {\ _ -> set})) g1))}
                            {\ _ -> set}
                            (var
                             (suc {snoc empty (\ _ -> set)}
                              {\ z2 ->
                                 el
                                 (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                  (var (zero {empty} {\ _ -> set})) z2)}
                              {\ _ -> set} (zero {empty} {\ _ -> set})))
                            (pair z1 v)))
                          (\ v1 -> set)))}
                   {\ _ -> set}
                   (var
                    (suc {snoc empty (\ _ -> set)}
                     {\ z1 ->
                        pi
                        (el
                         (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                          (var (zero {empty} {\ _ -> set})) z1))
                        (\ v ->
                           pi
                           (el
                            (eval
                             {snoc (snoc empty (\ _ -> set))
                              (\ g1 ->
                                 el
                                 (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                  (var (zero {empty} {\ _ -> set})) g1))}
                             {\ _ -> set}
                             (var
                              (suc {snoc empty (\ _ -> set)}
                               {\ z2 ->
                                  el
                                  (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                   (var (zero {empty} {\ _ -> set})) z2)}
                               {\ _ -> set} (zero {empty} {\ _ -> set})))
                             (pair z1 v)))
                           (\ v1 -> set))}
                     {\ g1 -> set} (zero {empty} {\ _ -> set})))
                   z))} (app {snoc
                                (snoc (snoc empty (\ z -> set))
                                 (\ z ->
                                    pi
                                    (el
                                     (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                      (var (zero {empty} {\ _ -> set})) z))
                                    (\ v ->
                                       pi
                                       (el
                                        (eval
                                         {snoc (snoc empty (\ _ -> set))
                                          (\ g1 ->
                                             el
                                             (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                              (var (zero {empty} {\ _ -> set})) g1))}
                                         {\ _ -> set}
                                         (var
                                          (suc {snoc empty (\ _ -> set)}
                                           {\ z1 ->
                                              el
                                              (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                               (var (zero {empty} {\ _ -> set})) z1)}
                                           {\ _ -> set} (zero {empty} {\ _ -> set})))
                                         (pair z v)))
                                       (\ v1 -> set))))
                                (\ z ->
                                   el
                                   (eval
                                    {snoc (snoc empty (\ z1 -> set))
                                     (\ z1 ->
                                        pi
                                        (el
                                         (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                          (var (zero {empty} {\ _ -> set})) z1))
                                        (\ v ->
                                           pi
                                           (el
                                            (eval
                                             {snoc (snoc empty (\ _ -> set))
                                              (\ g1 ->
                                                 el
                                                 (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                  (var (zero {empty} {\ _ -> set})) g1))}
                                             {\ _ -> set}
                                             (var
                                              (suc {snoc empty (\ _ -> set)}
                                               {\ z2 ->
                                                  el
                                                  (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                   (var (zero {empty} {\ _ -> set})) z2)}
                                               {\ _ -> set} (zero {empty} {\ _ -> set})))
                                             (pair z1 v)))
                                           (\ v1 -> set)))}
                                    {\ _ -> set}
                                    (var
                                     (suc {snoc empty (\ _ -> set)}
                                      {\ z1 ->
                                         pi
                                         (el
                                          (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                           (var (zero {empty} {\ _ -> set})) z1))
                                         (\ v ->
                                            pi
                                            (el
                                             (eval
                                              {snoc (snoc empty (\ _ -> set))
                                               (\ g1 ->
                                                  el
                                                  (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                   (var (zero {empty} {\ _ -> set})) g1))}
                                              {\ _ -> set}
                                              (var
                                               (suc {snoc empty (\ _ -> set)}
                                                {\ z2 ->
                                                   el
                                                   (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                    (var (zero {empty} {\ _ -> set})) z2)}
                                                {\ _ -> set} (zero {empty} {\ _ -> set})))
                                              (pair z1 v)))
                                            (\ v1 -> set))}
                                      {\ g1 -> set} (zero {empty} {\ _ -> set})))
                                    z))} {\ g ->
                                              el
                                              (eval
                                               {snoc (snoc empty (\ z -> set))
                                                (\ z ->
                                                   pi
                                                   (el
                                                    (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                     (var (zero {empty} {\ _ -> set})) z))
                                                   (\ v ->
                                                      pi
                                                      (el
                                                       (eval
                                                        {snoc (snoc empty (\ _ -> set))
                                                         (\ g1 ->
                                                            el
                                                            (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                             (var (zero {empty} {\ _ -> set})) g1))}
                                                        {\ _ -> set}
                                                        (var
                                                         (suc {snoc empty (\ _ -> set)}
                                                          {\ z1 ->
                                                             el
                                                             (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                              (var (zero {empty} {\ _ -> set})) z1)}
                                                          {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                        (pair z v)))
                                                      (\ v1 -> set)))}
                                               {\ _ -> set}
                                               (var
                                                (suc {snoc empty (\ _ -> set)}
                                                 {\ z ->
                                                    pi
                                                    (el
                                                     (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                      (var (zero {empty} {\ _ -> set})) z))
                                                    (\ v ->
                                                       pi
                                                       (el
                                                        (eval
                                                         {snoc (snoc empty (\ _ -> set))
                                                          (\ g1 ->
                                                             el
                                                             (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                              (var (zero {empty} {\ _ -> set})) g1))}
                                                         {\ _ -> set}
                                                         (var
                                                          (suc {snoc empty (\ _ -> set)}
                                                           {\ z1 ->
                                                              el
                                                              (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                               (var (zero {empty} {\ _ -> set})) z1)}
                                                           {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                         (pair z v)))
                                                       (\ v1 -> set))}
                                                 {\ g1 -> set} (zero {empty} {\ _ -> set})))
                                               (fst g))} (app {snoc
                                                                 (snoc (snoc empty (\ z -> set))
                                                                  (\ z ->
                                                                     pi
                                                                     (el
                                                                      (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                       (var (zero {empty} {\ _ -> set})) z))
                                                                     (\ v ->
                                                                        pi
                                                                        (el
                                                                         (eval
                                                                          {snoc (snoc empty (\ _ -> set))
                                                                           (\ g1 ->
                                                                              el
                                                                              (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                               (var (zero {empty} {\ _ -> set})) g1))}
                                                                          {\ _ -> set}
                                                                          (var
                                                                           (suc {snoc empty (\ _ -> set)}
                                                                            {\ z1 ->
                                                                               el
                                                                               (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                (var (zero {empty} {\ _ -> set})) z1)}
                                                                            {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                          (pair z v)))
                                                                        (\ v1 -> set))))
                                                                 (\ z ->
                                                                    el
                                                                    (eval
                                                                     {snoc (snoc empty (\ z1 -> set))
                                                                      (\ z1 ->
                                                                         pi
                                                                         (el
                                                                          (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                           (var (zero {empty} {\ _ -> set})) z1))
                                                                         (\ v ->
                                                                            pi
                                                                            (el
                                                                             (eval
                                                                              {snoc (snoc empty (\ _ -> set))
                                                                               (\ g1 ->
                                                                                  el
                                                                                  (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                   (var (zero {empty} {\ _ -> set})) g1))}
                                                                              {\ _ -> set}
                                                                              (var
                                                                               (suc {snoc empty (\ _ -> set)}
                                                                                {\ z2 ->
                                                                                   el
                                                                                   (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                    (var (zero {empty} {\ _ -> set})) z2)}
                                                                                {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                              (pair z1 v)))
                                                                            (\ v1 -> set)))}
                                                                     {\ _ -> set}
                                                                     (var
                                                                      (suc {snoc empty (\ _ -> set)}
                                                                       {\ z1 ->
                                                                          pi
                                                                          (el
                                                                           (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                            (var (zero {empty} {\ _ -> set})) z1))
                                                                          (\ v ->
                                                                             pi
                                                                             (el
                                                                              (eval
                                                                               {snoc (snoc empty (\ _ -> set))
                                                                                (\ g1 ->
                                                                                   el
                                                                                   (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                    (var (zero {empty} {\ _ -> set})) g1))}
                                                                               {\ _ -> set}
                                                                               (var
                                                                                (suc {snoc empty (\ _ -> set)}
                                                                                 {\ z2 ->
                                                                                    el
                                                                                    (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                     (var (zero {empty} {\ _ -> set})) z2)}
                                                                                 {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                               (pair z1 v)))
                                                                             (\ v1 -> set))}
                                                                       {\ g1 -> set} (zero {empty} {\ _ -> set})))
                                                                     z))} {\ g ->
                                                                               el
                                                                               (eval
                                                                                {snoc (snoc empty (\ z -> set))
                                                                                 (\ z ->
                                                                                    pi
                                                                                    (el
                                                                                     (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                      (var (zero {empty} {\ _ -> set})) z))
                                                                                    (\ v ->
                                                                                       pi
                                                                                       (el
                                                                                        (eval
                                                                                         {snoc (snoc empty (\ _ -> set))
                                                                                          (\ g1 ->
                                                                                             el
                                                                                             (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                              (var (zero {empty} {\ _ -> set})) g1))}
                                                                                         {\ _ -> set}
                                                                                         (var
                                                                                          (suc {snoc empty (\ _ -> set)}
                                                                                           {\ z1 ->
                                                                                              el
                                                                                              (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                               (var (zero {empty} {\ _ -> set})) z1)}
                                                                                           {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                                         (pair z v)))
                                                                                       (\ v1 -> set)))}
                                                                                {\ _ -> set}
                                                                                (var
                                                                                 (suc {snoc empty (\ _ -> set)}
                                                                                  {\ z ->
                                                                                     pi
                                                                                     (el
                                                                                      (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                       (var (zero {empty} {\ _ -> set})) z))
                                                                                     (\ v ->
                                                                                        pi
                                                                                        (el
                                                                                         (eval
                                                                                          {snoc (snoc empty (\ _ -> set))
                                                                                           (\ g1 ->
                                                                                              el
                                                                                              (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                               (var (zero {empty} {\ _ -> set})) g1))}
                                                                                          {\ _ -> set}
                                                                                          (var
                                                                                           (suc {snoc empty (\ _ -> set)}
                                                                                            {\ z1 ->
                                                                                               el
                                                                                               (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                                (var (zero {empty} {\ _ -> set})) z1)}
                                                                                            {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                                          (pair z v)))
                                                                                        (\ v1 -> set))}
                                                                                  {\ g1 -> set} (zero {empty} {\ _ -> set})))
                                                                                (fst g))} {\ g v ->
                                                                                               pi
                                                                                               (el
                                                                                                (eval
                                                                                                 {snoc (snoc empty (\ _ -> set))
                                                                                                  (\ g1 ->
                                                                                                     el
                                                                                                     (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                                      (var (zero {empty} {\ _ -> set})) g1))}
                                                                                                 {\ _ -> set}
                                                                                                 (var
                                                                                                  (suc {snoc empty (\ _ -> set)}
                                                                                                   {\ z1 ->
                                                                                                      el
                                                                                                      (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                                       (var (zero {empty} {\ _ -> set})) z1)}
                                                                                                   {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                                                 (pair (fst (fst g)) v)))
                                                                                               (\ v1 -> set)} (var (suc {snoc (snoc empty (\ _ -> set))
                                                                                                                          (\ z ->
                                                                                                                             pi
                                                                                                                             (el
                                                                                                                              (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                                                               (var (zero {empty} {\ _ -> set})) z))
                                                                                                                             (\ v ->
                                                                                                                                pi
                                                                                                                                (el
                                                                                                                                 (eval
                                                                                                                                  {snoc (snoc empty (\ _ -> set))
                                                                                                                                   (\ g1 ->
                                                                                                                                      el
                                                                                                                                      (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                                                                       (var (zero {empty} {\ _ -> set})) g1))}
                                                                                                                                  {\ _ -> set}
                                                                                                                                  (var
                                                                                                                                   (suc {snoc empty (\ _ -> set)}
                                                                                                                                    {\ z1 ->
                                                                                                                                       el
                                                                                                                                       (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                                                                        (var (zero {empty} {\ _ -> set})) z1)}
                                                                                                                                    {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                                                                                  (pair z v)))
                                                                                                                                (\ v1 -> set)))} {\ z ->
                                                                                                                                                     el
                                                                                                                                                     (eval
                                                                                                                                                      {snoc (snoc empty (\ z1 -> set))
                                                                                                                                                       (\ z1 ->
                                                                                                                                                          pi
                                                                                                                                                          (el
                                                                                                                                                           (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                                                                                            (var (zero {empty} {\ _ -> set})) z1))
                                                                                                                                                          (\ v ->
                                                                                                                                                             pi
                                                                                                                                                             (el
                                                                                                                                                              (eval
                                                                                                                                                               {snoc (snoc empty (\ _ -> set))
                                                                                                                                                                (\ g1 ->
                                                                                                                                                                   el
                                                                                                                                                                   (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                                                                                                    (var (zero {empty} {\ _ -> set})) g1))}
                                                                                                                                                               {\ _ -> set}
                                                                                                                                                               (var
                                                                                                                                                                (suc {snoc empty (\ _ -> set)}
                                                                                                                                                                 {\ z2 ->
                                                                                                                                                                    el
                                                                                                                                                                    (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                                                                                                     (var (zero {empty} {\ _ -> set})) z2)}
                                                                                                                                                                 {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                                                                                                               (pair z1 v)))
                                                                                                                                                             (\ v1 -> set)))}
                                                                                                                                                      {\ _ -> set}
                                                                                                                                                      (var
                                                                                                                                                       (suc {snoc empty (\ _ -> set)}
                                                                                                                                                        {\ z1 ->
                                                                                                                                                           pi
                                                                                                                                                           (el
                                                                                                                                                            (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                                                                                             (var (zero {empty} {\ _ -> set})) z1))
                                                                                                                                                           (\ v ->
                                                                                                                                                              pi
                                                                                                                                                              (el
                                                                                                                                                               (eval
                                                                                                                                                                {snoc (snoc empty (\ _ -> set))
                                                                                                                                                                 (\ g1 ->
                                                                                                                                                                    el
                                                                                                                                                                    (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                                                                                                     (var (zero {empty} {\ _ -> set})) g1))}
                                                                                                                                                                {\ _ -> set}
                                                                                                                                                                (var
                                                                                                                                                                 (suc {snoc empty (\ _ -> set)}
                                                                                                                                                                  {\ z2 ->
                                                                                                                                                                     el
                                                                                                                                                                     (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                                                                                                      (var (zero {empty} {\ _ -> set})) z2)}
                                                                                                                                                                  {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                                                                                                                (pair z1 v)))
                                                                                                                                                              (\ v1 -> set))}
                                                                                                                                                        {\ g1 -> set} (zero {empty} {\ _ -> set})))
                                                                                                                                                      z)} {\ g ->
                                                                                                                                                               pi
                                                                                                                                                               (el
                                                                                                                                                                (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                                                                                                 (var (zero {empty} {\ _ -> set})) (fst g)))
                                                                                                                                                               (\ v ->
                                                                                                                                                                  pi
                                                                                                                                                                  (el
                                                                                                                                                                   (eval
                                                                                                                                                                    {snoc (snoc empty (\ _ -> set))
                                                                                                                                                                     (\ g1 ->
                                                                                                                                                                        el
                                                                                                                                                                        (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                                                                                                         (var (zero {empty} {\ _ -> set})) g1))}
                                                                                                                                                                    {\ _ -> set}
                                                                                                                                                                    (var
                                                                                                                                                                     (suc {snoc empty (\ _ -> set)}
                                                                                                                                                                      {\ z1 ->
                                                                                                                                                                         el
                                                                                                                                                                         (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                                                                                                          (var (zero {empty} {\ _ -> set})) z1)}
                                                                                                                                                                      {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                                                                                                                    (pair (fst g) v)))
                                                                                                                                                                  (\ v1 -> set))} (zero {snoc empty (\ _ -> set)} {\ z ->
                                                                                                                                                              pi
                                                                                                                                                              (el
                                                                                                                                                               (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                                                                                                (var (zero {empty} {\ _ -> set})) z))
                                                                                                                                                              (\ v ->
                                                                                                                                                                 pi
                                                                                                                                                                 (el
                                                                                                                                                                  (eval
                                                                                                                                                                   {snoc (snoc empty (\ _ -> set))
                                                                                                                                                                    (\ g1 ->
                                                                                                                                                                       el
                                                                                                                                                                       (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                                                                                                        (var (zero {empty} {\ _ -> set})) g1))}
                                                                                                                                                                   {\ _ -> set}
                                                                                                                                                                   (var
                                                                                                                                                                    (suc {snoc empty (\ _ -> set)}
                                                                                                                                                                     {\ z1 ->
                                                                                                                                                                        el
                                                                                                                                                                        (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                                                                                                         (var (zero {empty} {\ _ -> set})) z1)}
                                                                                                                                                                     {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                                                                                                                   (pair z v)))
                                                                                                                                                                 (\ v1 -> set))}))) (var (zero {snoc (snoc empty (\ v -> set))
                                                                                                                                                                     (\ z ->
                                                                                                                                                                        pi
                                                                                                                                                                        (el
                                                                                                                                                                         (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                                                                                                          (var (zero {empty} {\ _ -> set})) z))
                                                                                                                                                                        (\ v ->
                                                                                                                                                                           pi
                                                                                                                                                                           (el
                                                                                                                                                                            (eval
                                                                                                                                                                             {snoc (snoc empty (\ _ -> set))
                                                                                                                                                                              (\ g1 ->
                                                                                                                                                                                 el
                                                                                                                                                                                 (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                                                                                                                  (var (zero {empty} {\ _ -> set})) g1))}
                                                                                                                                                                             {\ _ -> set}
                                                                                                                                                                             (var
                                                                                                                                                                              (suc {snoc empty (\ _ -> set)}
                                                                                                                                                                               {\ z1 ->
                                                                                                                                                                                  el
                                                                                                                                                                                  (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                                                                                                                   (var (zero {empty} {\ _ -> set})) z1)}
                                                                                                                                                                               {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                                                                                                                             (pair z v)))
                                                                                                                                                                           (\ v1 -> set)))} {\ z ->
                                                                                                                                                                     el
                                                                                                                                                                     (eval
                                                                                                                                                                      {snoc (snoc empty (\ z1 -> set))
                                                                                                                                                                       (\ z1 ->
                                                                                                                                                                          pi
                                                                                                                                                                          (el
                                                                                                                                                                           (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                                                                                                            (var (zero {empty} {\ _ -> set})) z1))
                                                                                                                                                                          (\ v ->
                                                                                                                                                                             pi
                                                                                                                                                                             (el
                                                                                                                                                                              (eval
                                                                                                                                                                               {snoc (snoc empty (\ _ -> set))
                                                                                                                                                                                (\ g1 ->
                                                                                                                                                                                   el
                                                                                                                                                                                   (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                                                                                                                    (var (zero {empty} {\ _ -> set})) g1))}
                                                                                                                                                                               {\ _ -> set}
                                                                                                                                                                               (var
                                                                                                                                                                                (suc {snoc empty (\ _ -> set)}
                                                                                                                                                                                 {\ z2 ->
                                                                                                                                                                                    el
                                                                                                                                                                                    (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                                                                                                                     (var (zero {empty} {\ _ -> set})) z2)}
                                                                                                                                                                                 {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                                                                                                                               (pair z1 v)))
                                                                                                                                                                             (\ v1 -> set)))}
                                                                                                                                                                      {\ _ -> set}
                                                                                                                                                                      (var
                                                                                                                                                                       (suc {snoc empty (\ _ -> set)}
                                                                                                                                                                        {\ z1 ->
                                                                                                                                                                           pi
                                                                                                                                                                           (el
                                                                                                                                                                            (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                                                                                                             (var (zero {empty} {\ _ -> set})) z1))
                                                                                                                                                                           (\ v ->
                                                                                                                                                                              pi
                                                                                                                                                                              (el
                                                                                                                                                                               (eval
                                                                                                                                                                                {snoc (snoc empty (\ _ -> set))
                                                                                                                                                                                 (\ g1 ->
                                                                                                                                                                                    el
                                                                                                                                                                                    (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                                                                                                                     (var (zero {empty} {\ _ -> set})) g1))}
                                                                                                                                                                                {\ _ -> set}
                                                                                                                                                                                (var
                                                                                                                                                                                 (suc {snoc empty (\ _ -> set)}
                                                                                                                                                                                  {\ z2 ->
                                                                                                                                                                                     el
                                                                                                                                                                                     (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                                                                                                                      (var (zero {empty} {\ _ -> set})) z2)}
                                                                                                                                                                                  {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                                                                                                                                (pair z1 v)))
                                                                                                                                                                              (\ v1 -> set))}
                                                                                                                                                                        {\ g1 -> set} (zero {empty} {\ _ -> set})))
                                                                                                                                                                      z)}))) (var (zero {snoc (snoc empty (\ v -> set))
                                                                                                                                                                                   (\ z ->
                                                                                                                                                                                      pi
                                                                                                                                                                                      (el
                                                                                                                                                                                       (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                                                                                                                        (var (zero {empty} {\ _ -> set})) z))
                                                                                                                                                                                      (\ v ->
                                                                                                                                                                                         pi
                                                                                                                                                                                         (el
                                                                                                                                                                                          (eval
                                                                                                                                                                                           {snoc (snoc empty (\ _ -> set))
                                                                                                                                                                                            (\ g1 ->
                                                                                                                                                                                               el
                                                                                                                                                                                               (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                                                                                                                                (var (zero {empty} {\ _ -> set})) g1))}
                                                                                                                                                                                           {\ _ -> set}
                                                                                                                                                                                           (var
                                                                                                                                                                                            (suc {snoc empty (\ _ -> set)}
                                                                                                                                                                                             {\ z1 ->
                                                                                                                                                                                                el
                                                                                                                                                                                                (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                                                                                                                                 (var (zero {empty} {\ _ -> set})) z1)}
                                                                                                                                                                                             {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                                                                                                                                           (pair z v)))
                                                                                                                                                                                         (\ v1 -> set)))} {\ z ->
                                                                                                                                                                                   el
                                                                                                                                                                                   (eval
                                                                                                                                                                                    {snoc (snoc empty (\ z1 -> set))
                                                                                                                                                                                     (\ z1 ->
                                                                                                                                                                                        pi
                                                                                                                                                                                        (el
                                                                                                                                                                                         (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                                                                                                                          (var (zero {empty} {\ _ -> set})) z1))
                                                                                                                                                                                        (\ v ->
                                                                                                                                                                                           pi
                                                                                                                                                                                           (el
                                                                                                                                                                                            (eval
                                                                                                                                                                                             {snoc (snoc empty (\ _ -> set))
                                                                                                                                                                                              (\ g1 ->
                                                                                                                                                                                                 el
                                                                                                                                                                                                 (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                                                                                                                                  (var (zero {empty} {\ _ -> set})) g1))}
                                                                                                                                                                                             {\ _ -> set}
                                                                                                                                                                                             (var
                                                                                                                                                                                              (suc {snoc empty (\ _ -> set)}
                                                                                                                                                                                               {\ z2 ->
                                                                                                                                                                                                  el
                                                                                                                                                                                                  (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                                                                                                                                   (var (zero {empty} {\ _ -> set})) z2)}
                                                                                                                                                                                               {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                                                                                                                                             (pair z1 v)))
                                                                                                                                                                                           (\ v1 -> set)))}
                                                                                                                                                                                    {\ _ -> set}
                                                                                                                                                                                    (var
                                                                                                                                                                                     (suc {snoc empty (\ _ -> set)}
                                                                                                                                                                                      {\ z1 ->
                                                                                                                                                                                         pi
                                                                                                                                                                                         (el
                                                                                                                                                                                          (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                                                                                                                           (var (zero {empty} {\ _ -> set})) z1))
                                                                                                                                                                                         (\ v ->
                                                                                                                                                                                            pi
                                                                                                                                                                                            (el
                                                                                                                                                                                             (eval
                                                                                                                                                                                              {snoc (snoc empty (\ _ -> set))
                                                                                                                                                                                               (\ g1 ->
                                                                                                                                                                                                  el
                                                                                                                                                                                                  (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                                                                                                                                   (var (zero {empty} {\ _ -> set})) g1))}
                                                                                                                                                                                              {\ _ -> set}
                                                                                                                                                                                              (var
                                                                                                                                                                                               (suc {snoc empty (\ _ -> set)}
                                                                                                                                                                                                {\ z2 ->
                                                                                                                                                                                                   el
                                                                                                                                                                                                   (eval {snoc empty (\ _ -> set)} {\ _ -> set}
                                                                                                                                                                                                    (var (zero {empty} {\ _ -> set})) z2)}
                                                                                                                                                                                                {\ _ -> set} (zero {empty} {\ _ -> set})))
                                                                                                                                                                                              (pair z1 v)))
                                                                                                                                                                                            (\ v1 -> set))}
                                                                                                                                                                                      {\ g1 -> set} (zero {empty} {\ _ -> set})))
                                                                                                                                                                                    z)}))))))
