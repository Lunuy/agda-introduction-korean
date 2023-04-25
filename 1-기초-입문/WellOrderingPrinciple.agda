
module WellOrderingPrinciple where
  
data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

data _⊎_ (A : Set) (B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

record Σ (A : Set) (B : A → Set) : Set where
  field
    fst : A
    snd : B fst

data ⊥ : Set where

explode : {A : Set} → ⊥ → A
explode ()

-- Negation
¬_ : Set → Set
¬ P = P → ⊥

¬¬_ : Set → Set
¬¬ P = (P → ⊥) → ⊥

¬¬¬-elim : {A : Set} → ¬¬ (¬ A) → ¬ A
¬¬¬-elim a = λ z₁ → a (λ z₂ → z₂ z₁)

¬¬⊥-elim : ¬¬ ⊥ → ⊥
¬¬⊥-elim a = a (λ z → z)

law-of-excluded-middle : (P : Set) → ¬¬ (P ⊎ (¬ P))
law-of-excluded-middle P a = a (inj₂ (λ x → a (inj₁ x)))

_>>=_ : {A B : Set} → ¬¬ A → (A → ¬¬ B) → ¬¬ B
a >>= f = λ z₁ → a (λ z₂ → f z₂ z₁)

pure : {A : Set} → A → ¬¬ A
pure a = λ f → f a


-- Util
case_of_ : {A : Set} {B : Set} → A → (A → B) → B
case x of f = f x


-- Equality
data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

sym : {A : Set} → {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : {A : Set} → {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl x = x

cong : {A B : Set} {a b : A} → (f : A → B) → a ≡ b → f a ≡ f b
cong f refl = refl


-- NotEmpty P 는 "자연수의 부분 집합 P는 공집합이 아니다"라는 명제를 나타내는 타입이다.
NotEmpty : (Nat → Set) → Set
NotEmpty P = Σ Nat P


-- a ≤ b라는 명제를 나타내는 타입
data _≤_ : Nat → Nat → Set where
  ≤-zero : {n : Nat}   → zero ≤ n
  ≤-suc  : {n m : Nat} → n ≤ m → (suc n) ≤ (suc m)

-- a < b라는 명제를 나타내는 타입
data _<_ : Nat → Nat → Set where
  <-zero : {n : Nat}   → zero < (suc n)
  <-suc  : {n m : Nat} → n < m → (suc n) < (suc m)

-- a ≤ b가 아니라면 b < a이다.
¬≤-to-< : {a b : Nat} → ¬ (a ≤ b) → b < a
¬≤-to-< {zero} {zero} f = explode (f ≤-zero)
¬≤-to-< {zero} {suc b} f = explode (f ≤-zero)
¬≤-to-< {suc a} {zero} f = <-zero
¬≤-to-< {suc a} {suc b} f = <-suc (¬≤-to-< (λ z → f (≤-suc z)))

-- a < 1 + b라면 a < b 또는 a = b이다.
<-right-suc-split : {a b : Nat} → a < (suc b) → (a < b) ⊎ (a ≡ b)
<-right-suc-split {zero}  {zero}  _         = inj₂ refl
<-right-suc-split {zero}  {suc _} _         = inj₁ <-zero
<-right-suc-split {suc a} {suc b} (<-suc c) = f (<-right-suc-split c)
  where
  f : (a < b) ⊎ (a ≡ b) → (suc a < suc b) ⊎ (suc a ≡ suc b)
  f (inj₁ x) = inj₁ (<-suc x)
  f (inj₂ x) = inj₂ (cong suc x)

-- a는 임의의 b에 대해 a < b거나 b ≤ a이다.
<-≤-split : (a b : Nat) → (a < b) ⊎ (b ≤ a)
<-≤-split a zero = inj₂ ≤-zero
<-≤-split zero (suc b) = inj₁ <-zero
<-≤-split (suc a) (suc b) = f (<-≤-split a b)
  where
  f : (a < b) ⊎ (b ≤ a) → (suc a < suc b) ⊎ (suc b ≤ suc a)
  f (inj₁ x) = inj₁ (<-suc x)
  f (inj₂ x) = inj₂ (≤-suc x)


-- 강한 수학적 귀납법
strong-nat-induction : {P : Nat → Set} → ((n : Nat) → ((m : Nat) → m < n → P m) → P n) → ((n : Nat) → P n)
strong-nat-induction {P} f n = con (suc n) n (n-<-suc-n n)
  where
    con : (n : Nat) → ((m : Nat) → m < n → P m)
    con zero m ()
    con (suc n) m a = g (<-right-suc-split a)
      where
      g : (m < n) ⊎ (m ≡ n) → P m
      g (inj₁ x)    = con n m x
      g (inj₂ refl) = f n (con n)
    
    n-<-suc-n : (n : Nat) → n < suc n
    n-<-suc-n zero = <-zero
    n-<-suc-n (suc n) = <-suc (n-<-suc-n n)


-- Min P n은 "P의 최소값이 n이다"라는 명제를 나타내는 타입
record Min (P : Nat → Set) (n : Nat) : Set where
  field
    min  : (m : Nat) → P m → (n ≤ m)
    in-P : P n

------------------------------------------ Double negation version

-- Well-ordering principle (Double negation version)
-- 공집합이 아닌 집합 P는 최소값을 갖는다.
well-ordering-principle : (P : Nat → Set) → NotEmpty P → ¬¬ (Σ Nat (Min P))
well-ordering-principle P not-empty-P = λ a → well-ordering-principle-contrapositive a not-empty-P
  where
    h : (n : Nat) → ((m : Nat) → m < n → ¬ P m) → (P n) → Min P n
    h n f p-n = record
      { min = min
      ; in-P = p-n
      }
      where
      min : (m : Nat) → P m → n ≤ m
      min m p-m = case (<-≤-split m n) of
        λ { (inj₁ m<n) → explode (f m m<n p-m)
          ; (inj₂ n≤m) → n≤m 
          }

    f : ¬ (Σ Nat (Min P)) → (n : Nat) → ((m : Nat) → m < n → ¬ P m) → ¬ P n
    f a k f = λ z →
      a record
        { fst = k
        ; snd = record
          { min = λ m p-m → Min.min (h k f z) m p-m
          ; in-P = z
          }
        }

    g : ((n : Nat) → ¬ P n) → ¬ NotEmpty P
    g a record { fst = fst ; snd = snd } = a fst snd
    
    well-ordering-principle-contrapositive : ¬ (Σ Nat (Min P)) → ¬ NotEmpty P
    well-ordering-principle-contrapositive a = g (strong-nat-induction {λ n → ¬ P n} (f a))


------------------------------------------ LEM Version

-- Law of Excluded Middle
data Dec (P : Set) : Set where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P

LEM : Set₁
LEM = (P : Set) → Dec P

-- LEM을 가정하면, ¬¬P로부터 P를 얻을 수 있다.
LEM-¬¬-elim : LEM → {P : Set} → (¬¬ P) → P
LEM-¬¬-elim lem {P} = g (lem P)
  where
  g : Dec P → (¬¬ P) → P
  g (yes p) _ = p
  g (no ¬p) p = explode (p ¬p)

-- LEM을 가정하면, ¬ A → ¬ B로부터 B → A를 얻을 수 있다.
LEM-contrapositive : LEM → {A B : Set} → (¬ A → ¬ B) → (B → A)
LEM-contrapositive lem f b = (LEM-¬¬-elim lem) (λ ¬a → (f ¬a) b)

-- Well-ordering principle (LEM version)
-- 공집합이 아닌 집합 P는 최소값을 갖는다.
LEM-well-ordering-principle : LEM → (P : Nat → Set) → NotEmpty P → Σ Nat (Min P)
LEM-well-ordering-principle lem P = LEM-contrapositive lem well-ordering-principle-contrapositive
  where
    h : (n : Nat) → ((m : Nat) → m < n → ¬ P m) → (P n) → Min P n
    h n f p-n = record
      { min = min
      ; in-P = p-n
      }
      where
      min : (m : Nat) → P m → n ≤ m
      min m p-m = case (<-≤-split m n) of
        λ { (inj₁ m<n) → explode (f m m<n p-m)
          ; (inj₂ n≤m) → n≤m 
          }

    f : ¬ (Σ Nat (Min P)) → (n : Nat) → ((m : Nat) → m < n → ¬ P m) → ¬ P n
    f a k f = λ z →
      a record
        { fst = k
        ; snd = record
          { min = λ m p-m → Min.min (h k f z) m p-m
          ; in-P = z
          }
        }

    g : ((n : Nat) → ¬ P n) → ¬ NotEmpty P
    g a record { fst = fst ; snd = snd } = a fst snd
    
    well-ordering-principle-contrapositive : ¬ (Σ Nat (Min P)) → ¬ NotEmpty P
    well-ordering-principle-contrapositive a = g (strong-nat-induction {λ n → ¬ P n} (f a))


-- 이 예시에서는 둘의 차이가 별로 크지 않지만, LEM을 사용하는 것이 Double negation을 사용하는 것보다 훨씬 간단할 수 있다.