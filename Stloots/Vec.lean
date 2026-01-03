inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)
deriving Repr

open Vec

def length (_v : Vec α n) : Nat := n

def head : Vec α (n + 1) → α
  | cons x _ => x

def head? : Vec α n → Option α
  | nil => none
  | cons x _ => some x

def headD (v : Vec α n) (fallback : α) : α :=
  match v with
  | nil => fallback
  | cons x _ => x

def tail : Vec α (n + 1) → Vec α n
  | cons _ xs => xs

def map (f : α → β) : Vec α n → Vec β n
  | nil => nil
  | cons x xs => cons (f x) (map f xs)

def append (a : α) : Vec α n → Vec α (n + 1)
  | nil => cons a nil
  | cons x xs => cons x (append a xs)

def concat : Vec α n → Vec α m → Vec α (m + n)
  | nil, ys => ys
  | cons x xs, ys => cons x (concat xs ys)

def replicate (n : Nat) (a : α) : Vec α n :=
  match n with
  | 0 => nil
  | n + 1 => cons a (replicate n a)

def zip : Vec α n → Vec β n → Vec (α × β) n
  | nil, _ => nil
  | cons x xs, cons y ys => cons (x, y) (zip xs ys)

def zipWith (f : α → β → ω) : Vec α n → Vec β n → Vec ω n
  | nil, _ => nil
  | cons x xs, cons y ys => cons (f x y) (zipWith f xs ys)

def diagonal : Vec (Vec α n) n → Vec α n
  | nil => nil
  | cons (cons x _) xss => cons x (diagonal (map tail xss))
