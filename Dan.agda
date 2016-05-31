open import Preliminaries
open Nat

module Dan where

data Tp : Set where
  P : Tp
  Q : Tp

data Ctx : Set where
  · : Ctx
  sCtx : Tp → Ctx
  _,_ : Ctx → Ctx → Ctx

data _empty : Ctx → Set where
  sinE : · empty
  mulE : ∀ {Γ₁ Γ₂} → Γ₁ empty → Γ₂ empty → (Γ₁ , Γ₂) empty

data _decTo_and_ : Ctx → Ctx → Ctx → Set where
  SD : ∀{A Γ} → Γ empty → sCtx A decTo sCtx A and Γ
  MD1 : ∀ {A Γ₁' Γ₁ Γ₂} → Γ₁ decTo sCtx A and Γ₁' → (Γ₁ , Γ₂) decTo sCtx A and (Γ₁' , Γ₂)
  MD2 : ∀ {A Γ₂' Γ₁ Γ₂} → Γ₂ decTo sCtx A and Γ₂' → (Γ₁ , Γ₂) decTo sCtx A and (Γ₁ , Γ₂')

data _≡_ : Ctx → Ctx → Set where
  emp : ∀{Γ₁ Γ₂} → Γ₁ empty → Γ₂ empty → Γ₁ ≡ Γ₂
  decom : ∀{Γ Γ' Δ Δ' A} → Γ decTo sCtx A and Γ' → Δ decTo sCtx A and Δ' → Γ' ≡ Δ' → Γ ≡ Δ

data _⊢s_ : Ctx → Ctx → Set where
  emptySub : · ⊢s ·
  var : ∀ {A} → (sCtx A) ⊢s (sCtx A)
  comma : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} → Γ₁ ⊢s Δ₁ → Γ₂ ⊢s Δ₂ → (Γ₁ , Γ₂) ⊢s (Δ₁ , Δ₂)
  equiv : ∀ {Γ Γ' Δ Δ'} → Γ ≡ Γ' → Γ' ⊢s Δ' → Δ' ≡ Δ → Γ ⊢s Δ

data _size_ : Ctx → Nat → Set where
  s0 : {Γ : Ctx} → Γ empty → Γ size 0
  s1 : {A : Tp} → sCtx A size 1
  sm : {Γ Δ : Ctx}{A : Tp}{n : Nat} → Γ decTo sCtx A and Δ → Δ size n → Γ size (S n)


lemmaEmptyDecom : ∀{Γ A Δ} → Γ empty → Γ decTo sCtx A and Δ → Void
lemmaEmptyDecom sinE ()
lemmaEmptyDecom (mulE empt empt₁) (MD1 decpf) = lemmaEmptyDecom empt decpf
lemmaEmptyDecom (mulE empt empt₁) (MD2 decpf) = lemmaEmptyDecom empt₁ decpf

lemma : ∀{Γ Δ} → Γ empty → Γ ≡ Δ → Δ empty
lemma sinE (emp x x₁) = x₁
lemma sinE (decom x x₁ pf) = abort (lemmaEmptyDecom sinE x)
lemma (mulE empt empt₁) (emp x x₁) = x₁
lemma (mulE {Γ₁}{Γ₂} empt empt₁) (decom x x₁ pf) = abort (lemmaEmptyDecom (mulE empt empt₁) x)

emptyCtxSizeLemma : ∀ {Γ Δ n} → Γ empty → Δ size n → (Γ , Δ) size n
emptyCtxSizeLemma empt (s0 x) = s0 (mulE empt x)
emptyCtxSizeLemma empt s1 = sm (MD2 (SD empt)) (s0 (mulE empt empt))
emptyCtxSizeLemma empt (sm x size) = sm (MD2 x) (emptyCtxSizeLemma empt size)

addSizesLemma : ∀{Γ Δ n m} → Γ size n → Δ size m → (Γ , Δ) size (n + m)
addSizesLemma {·} (s0 x) (s0 x₁) = s0 (mulE x x₁)
addSizesLemma {·} (s0 x) s1 = sm (MD2 (SD x)) (s0 (mulE x x))
addSizesLemma {·} (s0 x) (sm x₁ size2) = sm (MD2 x₁) (addSizesLemma (s0 x) size2)
addSizesLemma {·} (sm () size1) size2
addSizesLemma {sCtx x} (s0 ()) size2
addSizesLemma {sCtx x} s1 (s0 x₁) = sm (MD1 (SD x₁)) (s0 (mulE x₁ x₁))
addSizesLemma {sCtx x} s1 s1 = sm (MD2 (SD sinE)) (sm (MD1 (SD sinE)) (s0 (mulE sinE sinE)))
addSizesLemma {sCtx x} s1 (sm x₁ size2) = sm (MD2 x₁) (addSizesLemma s1 size2)
addSizesLemma {sCtx A} (sm (SD x) (s0 x₁)) (s0 x₂) = addSizesLemma s1 (s0 x₂)
addSizesLemma {sCtx A₁} (sm (SD x) (s0 x₁)) s1 = addSizesLemma s1 s1
addSizesLemma {sCtx A} (sm (SD x) (s0 x₁)) (sm x₂ size2) = sm (MD2 x₂) (addSizesLemma s1 size2)
addSizesLemma {sCtx A₁} (sm (SD ()) s1) size2
addSizesLemma {sCtx A} (sm (SD x) (sm x₁ size1)) size2 = abort (lemmaEmptyDecom x x₁)
addSizesLemma {Γ₁ , Γ₂} (s0 (mulE x x₁)) (s0 x₂) = s0 (mulE (mulE x x₁) x₂)
addSizesLemma {Γ₁ , Γ₂} (s0 (mulE x x₁)) s1 = sm (MD2 (SD x₁)) (s0 (mulE (mulE x x₁) x₁))
addSizesLemma {Γ₁ , Γ₂} (s0 (mulE x x₁)) (sm x₂ size2) = sm (MD2 x₂) (emptyCtxSizeLemma (mulE x x₁) size2)
addSizesLemma {Γ₁ , Γ₂} (sm x size1) (s0 x₁) = sm (MD1 x) (addSizesLemma size1 (s0 x₁))
addSizesLemma {Γ₁ , Γ₂} (sm x size1) s1 = sm (MD1 x) (addSizesLemma size1 s1)
addSizesLemma {Γ₁ , Γ₂} (sm x size1) (sm x₁ size2) = sm (MD1 x) (addSizesLemma size1 (sm x₁ size2))

findSize : (Γ : Ctx) → Σ[ n ∈ Nat ] (Γ size n)
findSize · = Z , s0 sinE
findSize (sCtx x) = S Z , s1
findSize (Γ₁ , Γ₂) with findSize Γ₁ | findSize Γ₂
... | (n1 , size1) | (n2 , size2) = (n1 + n2) , addSizesLemma size1 size2

refl : ∀{Γ n} → Γ size n → Γ ≡ Γ
refl (s0 x) = emp x x
refl s1 = decom (SD sinE) (SD sinE) (emp sinE sinE)
refl (sm x size) = decom x x (refl size)

comm : ∀{Γ₁ Γ₂ n} → (Γ₁ , Γ₂) size n → (Γ₁ , Γ₂) ≡ (Γ₂ , Γ₁)
comm (s0 (mulE x x₁)) = emp (mulE x x₁) (mulE x₁ x)
comm (sm (MD1 x) size) = decom (MD1 x) (MD2 x) (comm size)
comm (sm (MD2 x) size) = decom (MD2 x) (MD1 x) (comm size)

assoc : ∀{Γ₁ Γ₂ Γ₃ n} → (Γ₁ , (Γ₂ , Γ₃)) size n → (Γ₁ , (Γ₂ , Γ₃)) ≡ ((Γ₁ , Γ₂) , Γ₃)
assoc (s0 (mulE x (mulE x₁ x₂))) = emp (mulE x (mulE x₁ x₂)) (mulE (mulE x x₁) x₂)
assoc (sm (MD1 x) size) = decom (MD1 x) (MD1 (MD1 x)) (assoc size)
assoc (sm (MD2 (MD1 x)) size) = decom (MD2 (MD1 x)) (MD1 (MD2 x)) (assoc size)
assoc (sm (MD2 (MD2 x)) size) = decom (MD2 (MD2 x)) (MD2 x) (assoc size)

sym : ∀{Γ₁ Γ₂} → Γ₁ ≡ Γ₂ → Γ₂ ≡ Γ₁
sym (emp x x₁) = emp x₁ x
sym (decom x x₁ pf) = decom x₁ x (sym pf)

cong : ∀{Γ Γ' Δ Δ'} → Γ ≡ Δ → Γ' ≡ Δ' → (Γ , Γ') ≡ (Δ , Δ')
cong (emp x x₁) (emp x₂ x₃) = emp (mulE x x₂) (mulE x₁ x₃)
cong (emp x x₁) (decom x₂ x₃ pf2) = decom (MD2 x₂) (MD2 x₃) (cong (emp x x₁) pf2)
cong (decom x x₁ pf1) (emp x₂ x₃) = decom (MD1 x) (MD1 x₁) (cong pf1 (emp x₂ x₃))
cong (decom x x₁ pf1) (decom x₂ x₃ pf2) = decom (MD1 x) (MD1 x₁) (cong pf1 (decom x₂ x₃ pf2))

transHelper : ∀{Γ A B Γ₁ Γ₂} → Γ decTo sCtx A and Γ₁ → Γ decTo sCtx B and Γ₂ → Either (sCtx A ≡ sCtx B × Γ₁ ≡ Γ₂) (Σ[ Δ₁ ∈ Ctx ] Σ[ Δ₂ ∈ Ctx ] (Γ₁ decTo sCtx B and Δ₁ × Γ₂ decTo sCtx A and Δ₂ × Δ₁ ≡ Δ₂))
transHelper {·} () dec2
transHelper {sCtx A} (SD x) (SD x₁) = Inl (decom (SD x₁) (SD x₁) (emp x₁ x₁) , emp x x₁)
transHelper {Γ₁ , Γ₂} (MD1 dec1) (MD1 dec2) with transHelper dec1 dec2
transHelper {Γ₁ , Γ₂} (MD1 dec1) (MD1 dec2) | Inl (emp () x₁ , ctxeq)
transHelper {Γ₁ , Γ₂} (MD1 dec1) (MD1 dec2) | Inl (decom (SD x) (SD x₁) seq , ctxeq) = Inl ((decom (SD x) (SD x₁) seq) , (cong ctxeq (refl (snd (findSize Γ₂)))))
transHelper {Γ₁ , Γ₂} (MD1 dec1) (MD1 dec2) | Inr (Δ₁ , Δ₂ , dec3 , dec4 , eq) = Inr ((Δ₁ , Γ₂) , (Δ₂ , Γ₂) , MD1 dec3 , MD1 dec4 , cong eq (refl (snd (findSize Γ₂))))
transHelper {Γ₁ , Γ₂} (MD1 dec1) (MD2 dec2) = Inr (_ , _ , MD2 dec2 , MD1 dec1 , refl (snd (findSize _)))
transHelper {Γ₁ , Γ₂} (MD2 dec1) (MD1 dec2) = Inr (_ , _ , MD1 dec2 , MD2 dec1 , refl (snd (findSize _)))
transHelper {Γ₁ , Γ₂} (MD2 dec1) (MD2 dec2) with transHelper dec1 dec2
transHelper {Γ₁ , Γ₂} (MD2 dec1) (MD2 dec2) | Inl (emp () x₁ , ctxeq)
transHelper {Γ₁ , Γ₂} (MD2 dec1) (MD2 dec2) | Inl (decom (SD x) (SD x₁) seq , ctxeq) = Inl ((decom (SD x) (SD x₁) seq) , (cong (refl (snd (findSize Γ₁))) ctxeq))
transHelper {Γ₁ , Γ₂} (MD2 dec1) (MD2 dec2) | Inr (Δ₁ , Δ₂ , dec3 , dec4 , eq) = Inr ((Γ₁ , Δ₁) , (Γ₁ , Δ₂) , MD2 dec3 , MD2 dec4 , cong (refl (snd (findSize Γ₁))) eq)

transNewHelper : ∀{Γ A B Γ₁ Γ₂} → Γ decTo sCtx A and Γ₁ → Γ₁ decTo sCtx B and Γ₂ → Σ[ Γ₃ ∈ Ctx ] (Γ decTo sCtx B and Γ₃ × Γ₃ decTo sCtx A and Γ₂)
transNewHelper (SD ()) (SD x₁)
transNewHelper (SD (mulE x x₁)) (MD1 dec2) = abort (lemmaEmptyDecom x dec2)
transNewHelper (SD (mulE x x₁)) (MD2 dec2) = abort (lemmaEmptyDecom x₁ dec2)
transNewHelper (MD1 dec1) (MD1 dec2) with transNewHelper dec1 dec2
transNewHelper (MD1 dec1) (MD1 dec2) | Γ₃ , dec3 , dec4 = (Γ₃ , _) , MD1 dec3 , MD1 dec4
transNewHelper {Γ = (Γ₁ , Γ₂)} (MD1 dec1) (MD2 {Γ₂' = Γ₂'} dec2) = (Γ₁ , Γ₂') , MD2 dec2 , MD1 dec1
transNewHelper {Γ = (Γ₁ , Γ₂)} (MD2 dec1) (MD1 {Γ₁' = Γ₁'} dec2) = (Γ₁' , Γ₂) , MD1 dec2 , MD2 dec1
transNewHelper (MD2 dec1) (MD2 dec2) with transNewHelper dec1 dec2
transNewHelper (MD2 dec1) (MD2 dec2) | Γ₃ , dec3 , dec4 = (_ , Γ₃) , MD2 dec3 , MD2 dec4

mutual
  decdSize : ∀{Γ Δ A n} → Γ decTo sCtx A and Δ → Γ size (S n) → Δ size n
  decdSize (SD x) s1 = s0 x
  decdSize dec (sm x size) with transHelper dec x
  decdSize dec (sm x size) | Inl (emp () x₂ , eq2)
  decdSize dec (sm x size) | Inl (decom (SD x₁) (SD x₂) eq1 , eq2) = equivSameSize eq2 size
  decdSize {Γ} {Δ₁} {A} {Z} dec (sm x (s0 x₁)) | Inr (Δ₂ , Δ₃ , dec3 , dec4 , eq) = abort (lemmaEmptyDecom x₁ dec4)
  decdSize {Γ} {Δ} {A} {S n} dec (sm x size) | Inr (Δ₂ , Δ₃ , dec3 , dec4 , eq) with decdSize dec4 size
  decdSize {Γ} {Δ₁} {A} {S Z} dec (sm x₁ size) | Inr (Δ₂ , Δ₃ , dec3 , dec4 , eq) | s0 x = sm dec3 (s0 (lemma x (sym eq)))
  decdSize {Γ} {Δ₁} {A} {S (S n)} dec (sm x size) | Inr (Δ₂ , Δ₃ , dec3 , dec4 , eq) | size2 = sm dec3 (equivSameSize eq size2)

  equivSameSize : ∀{Γ Δ n} → Γ ≡ Δ → Δ size n → Γ size n
  equivSameSize (emp x x₁) (s0 x₂) = s0 x
  equivSameSize (emp x ()) s1
  equivSameSize (emp x x₁) (sm x₂ size) = abort (lemmaEmptyDecom x₁ x₂)
  equivSameSize (decom x x₁ eqpf) (s0 x₂) = abort (lemmaEmptyDecom x₂ x₁)
  equivSameSize (decom x (SD x₁) eqpf) s1 = sm x (equivSameSize eqpf (s0 x₁))
  equivSameSize (decom x x₁ eqpf) (sm x₂ size) with transHelper x₁ x₂
  equivSameSize (decom x₄ x₁ eqpf) (sm x₂ size) | Inl (emp () x₃ , eq2)
  equivSameSize (decom x₄ x₁ eqpf) (sm x₂ size) | Inl (decom (SD x) (SD x₃) eq1 , eq2) with (decdSize x₁ (sm x₂ size))
  ... | size2 with equivSameSize eqpf size2
  ... | size3 = sm x₄ size3
  equivSameSize (decom x₃ x₁ eqpf) (sm {_} {Δ} {A₁} {Z} x₂ (s0 x)) | Inr (Δ₂ , Δ₃ , dec3 , dec4 , eq2) = abort (lemmaEmptyDecom x dec4)
  equivSameSize (decom x₃ x₁ eqpf) (sm {_} {Δ₁} {A₁} {S n} x₂ size) | Inr (Δ₂ , Δ₃ , dec3 , dec4 , eq2) with decdSize dec4 size | decdSize x₁ (sm x₂ size)
  ... | size2 | size3 = sm x₃ (equivSameSize eqpf size3)

  decProp : ∀{Γ Γ' A Δ n} → Γ decTo sCtx A and Δ
                      → Γ ≡ Γ'
                      → Γ size n
                      → Σ[ Δ' ∈ Ctx ] (Γ' decTo sCtx A and Δ' × Δ ≡ Δ')
  decProp (SD x) (emp () x₂) size
  decProp (SD x) (decom (SD x₁) x₂ eqpf) (s0 ())
  decProp (SD x) (decom (SD x₁) x₂ eqpf) s1 = _ , (x₂ , (emp x (lemma x₁ eqpf)))
  decProp (SD x) (decom (SD x₁) x₂ eqpf) (sm x₃ size) = _ , (x₂ , (emp x (lemma x₁ eqpf)))
  decProp (MD1 decpf) (emp x x₁) size = abort (lemmaEmptyDecom x (MD1 decpf))
  decProp (MD2 decpf) (emp (mulE x x₁) x₂) size = abort (lemmaEmptyDecom x₁ decpf)
  decProp decpf (decom x x₁ eqpf) size with transHelper decpf x
  decProp decpf (decom x x₃ eqpf) size | Inl (emp () x₂ , eq2)
  decProp {Γ} {Γ'''} {A} {Δ} {Z} decpf (decom x x₃ eqpf) (s0 x₄) | Inl (decom (SD x₁) (SD x₂) eq1 , eq2) = abort (lemmaEmptyDecom x₄ x)
  decProp {Γ} {Γ'''} {A} {Δ} {S n} decpf (decom x x₃ eqpf) size | Inl (decom (SD x₁) (SD x₂) eq1 , eq2) with (decdSize decpf size)
  ... | size2 with equivSameSize (sym eq2) size2
  ... | size3 = _ , (x₃ , trans eq2 eqpf size2 size3 (equivSameSize (sym eqpf) size3))
  decProp {Γ} {Γ''} {A} {Δ} {Z} decpf (decom x x₂ eqpf) (s0 x₁) | Inr (Δ₁ , Δ₂ , dec3 , dec4 , eq2) = abort (lemmaEmptyDecom x₁ x)
  decProp {Γ} {Γ''} {A} {Δ} {S n} decpf (decom x x₂ eqpf) size | Inr (Δ₁ , Δ₂ , dec3 , dec4 , eq2) with (decdSize x size)
  ... | size2 with decProp dec4 eqpf size2
  ... | Δ₃ , dec5 , eq3 with transNewHelper x₂ dec5
  decProp {Γ₁} {Γ'} {A} {Δ} {S Z} decpf (decom x₁ x₂ eqpf) size | Inr (Δ₁ , Δ₂ , dec3 , dec4 , eq2) | s0 x | Δ₃ , dec5 , eq3 | Δ₄ , dec6 , dec7 = abort (lemmaEmptyDecom x dec4)
  decProp {Γ} {Γ'} {A} {Δ} {S (S n)} decpf (decom x x₂ eqpf) size | Inr (Δ₁ , Δ₂ , dec3 , dec4 , eq2) | size2 | Δ₃ , dec5 , eq3 | Δ₄ , dec6 , dec7 = Δ₄ , (dec6 , (decom dec3 dec7 (trans eq2 eq3 (decdSize dec3 (decdSize decpf size)) (decdSize dec4 size2) (decdSize dec5 (equivSameSize (sym eqpf) size2)))))

  trans : ∀{Γ₁ Γ₂ Γ₃ n} → Γ₁ ≡ Γ₂ → Γ₂ ≡ Γ₃ → Γ₁ size n → Γ₂ size n → Γ₃ size n → Γ₁ ≡ Γ₃
  trans (emp x x₁) (emp x₂ x₃) (s0 x₄) size2 size3 = emp x₄ x₃
  trans (emp x x₁) (decom x₂ x₃ eq2) (s0 x₄) size2 size3 = abort (lemmaEmptyDecom x₁ x₂)
  trans (decom x x₁ eq1) eq2 (s0 x₂) size2 size3 = abort (lemmaEmptyDecom x₂ x)
  trans (emp () x₁) eq2 s1 size2 size3 
  trans (decom (SD x) x₁ eq1) (emp x₂ x₃) s1 size2 size3 = abort (lemmaEmptyDecom x₂ x₁)
  trans (decom (SD x) x₁ eq1) (decom x₂ x₃ eq2) s1 size2 size3 with transHelper x₁ x₂ | decdSize x₁ size2 | decdSize x₂ size2 | decdSize x₃ size3
  trans (decom (SD x) x₁ eq1) (decom x₂ x₃ eq2) s1 size2 size3 | Inl (emp () x₅ , snd) | size5 | size6 | size7
  trans (decom (SD x₅) x₁ eq1) (decom x₂ x₃ eq2) s1 size2 size3 | Inl (decom (SD x) (SD x₄) fst , snd) | size5 | size6 | size7 = decom (SD x₅) x₃ (trans eq1 (trans snd eq2 size5 size6 size7) (s0 x₅) size5 size7)
  trans (decom (SD x) x₁ eq1) (decom x₂ x₃ eq2) s1 size2 size3 | Inr (Δ₁ , Δ₂ , dec1 , dec2 , eq) | size5 | size6 | size7 = abort (lemmaEmptyDecom (lemma x eq1) dec1)
  trans (emp x x₁) (emp x₂ x₃) (sm x₄ size) size2 size3 = emp x x₃
  trans (emp x x₁) (decom x₂ x₃ eq2) (sm x₄ size) size2 size3 = abort (lemmaEmptyDecom x₁ x₂)
  trans (decom x x₁ eq1) (emp x₂ x₃) (sm x₄ size) size2 size3 = abort (lemmaEmptyDecom x₂ x₁)
  trans (decom x x₁ eq1) (decom x₂ x₃ eq2) (sm x₄ size) size2 size3 with transHelper x₁ x₂ | decdSize x (sm x₄ size) | decdSize x₁ size2 | decdSize x₃ size3 | decdSize x₂ size2
  trans (decom x₄ x₁ eq1) (decom x₂ x₅ eq2) (sm x₆ size) size2 size3 | Inl (emp () x₃ , eq4) | _ | _ | _ | _
  trans (decom x₄ x₁ eq1) (decom x₂ x₅ eq2) (sm x₆ size) size2 size3 | Inl (decom (SD x) (SD x₃) eq3 , eq4) | size4 | size5 | size6 | size7 = decom x₄ x₅ (trans eq1 (trans eq4 eq2 size5 size7 size6) size4 size5 size6)
  trans (decom x₃ x₁ eq1) (decom x₂ x₄ eq2) (sm x₅ size) size2 size3 | Inr (Δ₁ , Δ₂ , dec1 , dec2 , eq) | size4 | size5 | size6 | size7 with decProp dec1 (sym eq1) size5 | decProp dec2 eq2 size7
  ... | Δ₃ , dec3 , eq3 | Δ₄ , dec4 , eq4 with transNewHelper x₄ dec4
  trans (decom x₃ x₁ eq1) (decom x₂ x₄ eq2) (sm {_} {Δ} {A₂} {Z} x₅ size) size2 size3 | Inr (Δ₁ , Δ₂ , dec1 , dec2 , eq) | s0 x | size5 | size6 | size7 | Δ₃ , dec3 , eq3 | Δ₄ , dec4 , eq4 | Γ₄ , dec5 , dec6 = abort (lemmaEmptyDecom x dec3)
  trans (decom x₃ x₁ eq1) (decom x₂ x₄ eq2) (sm {_} {Δ} {A₂} {S n} x₅ size) size2 size3 | Inr (Δ₁ , Δ₂ , dec1 , dec2 , eq) | size4 | size5 | size6 | size7 | Δ₃ , dec3 , eq3 | Δ₄ , dec4 , eq4 | Γ₄ , dec5 , dec6 = decom x₃ dec5 (decom dec3 dec6 (trans (sym eq3) (trans eq eq4 (decdSize dec1 size5) (decdSize dec2 size7) (decdSize dec4 size6)) (decdSize dec3 size4) (decdSize dec1 size5) (decdSize dec4 size6)))

unitL : ∀ {Γ} → (· , Γ) ≡ Γ
unitL {·} = emp (mulE sinE sinE) sinE
unitL {sCtx x} = decom (MD2 (SD sinE)) (SD sinE) (emp (mulE sinE sinE) sinE)
unitL {Γ₁ , Γ₂} = trans (assoc (snd (findSize (· , (Γ₁ , Γ₂))))) (cong (unitL {Γ₁}) (refl {Γ₂} (snd (findSize Γ₂)))) (snd (findSize (· , (Γ₁ , Γ₂)))) (snd (findSize ((· , Γ₁) , Γ₂))) (snd (findSize (Γ₁ , Γ₂)))

unitRhelp1 : ∀ {Γ n} → Γ size n → (Γ , ·) size n
unitRhelp1 (s0 x) = s0 (mulE x sinE)
unitRhelp1 s1 = sm (MD1 (SD sinE)) (s0 (mulE sinE sinE))
unitRhelp1 (sm x size) = sm (MD1 x) (unitRhelp1 size)

unitRhelp2 : ∀ {Γ₁ Γ₂ n} → (Γ₁ , Γ₂) size n → (Γ₁ , (Γ₂ , ·)) size n
unitRhelp2 (s0 (mulE x x₁)) = s0 (mulE x (mulE x₁ sinE))
unitRhelp2 (sm (MD1 x) size) = sm (MD1 x) (unitRhelp2 size)
unitRhelp2 (sm (MD2 x) size) = sm (MD2 (MD1 x)) (unitRhelp2 size)

unitR : ∀ {Γ} → (Γ , ·) ≡ Γ
unitR {·} = emp (mulE sinE sinE) sinE
unitR {sCtx x} = decom (MD1 (SD sinE)) (SD sinE) (emp (mulE sinE sinE) sinE)
unitR {Γ₁ , Γ₂} with findSize (Γ₁ , Γ₂) | findSize Γ₁ | findSize Γ₂
unitR {Γ₁ , Γ₂} | n+m , sizeboth | n , size1 | m , size2 = trans (sym (assoc (snd (findSize (Γ₁ , (Γ₂ , ·)))))) (cong (refl size1) unitR) (unitRhelp1 sizeboth) (unitRhelp2 sizeboth) sizeboth



-- emptyEquiv : ∀ {Γ₁ Γ₂} → · ≡ (Γ₁ , Γ₂) → · ≡ Γ₁ × · ≡ Γ₂
-- emptyEquiv (emp x (mulE x₁ x₂)) = emp x x₁ , emp x x₂
-- emptyEquiv (decom () x₁ pf)

-- emptySubLemma : ∀ {Γ Δ} → Γ ⊢s Δ → Δ empty → Γ empty
-- emptySubLemma emptySub empt = empt
-- emptySubLemma var ()
-- emptySubLemma (comma sub sub₁) (mulE empt empt₁) = mulE (emptySubLemma sub empt) (emptySubLemma sub₁ empt₁)
-- emptySubLemma (equiv x sub x₁) empt = lemma (emptySubLemma sub (lemma empt (sym x₁))) (sym x)

-- lemmaSingleEmpty : ∀ {Γ A Δ} → Γ decTo sCtx A and Δ → · ≡ Δ → Γ ≡ sCtx A
-- lemmaSingleEmpty (SD x) empteq = decom (SD x) (SD x) (emp x x)
-- lemmaSingleEmpty (MD1 decpf) empteq = decom (MD1 decpf) (SD sinE) (sym empteq)
-- lemmaSingleEmpty (MD2 decpf) empteq = decom (MD2 decpf) (SD sinE) (sym empteq)

-- emptyLemma : ∀ {Γ} → Γ empty → · ≡ Γ
-- emptyLemma sinE = emp sinE sinE
-- emptyLemma (mulE pf pf₁) = emp sinE (mulE pf pf₁)


-- subEquivs : ∀ {Γ Δ} → Γ ⊢s Δ → Γ ≡ Δ
-- subEquivs emptySub = emp sinE sinE
-- subEquivs var = decom (SD sinE) (SD sinE) (emp sinE sinE)
-- subEquivs (comma sub sub₁) = cong (subEquivs sub) (subEquivs sub₁)
-- subEquivs (equiv x sub x₁) = trans (trans x (subEquivs sub)) x₁

-- reflSub : ∀ {Γ} → Γ ⊢s Γ
-- reflSub {·} = emptySub
-- reflSub {sCtx x} = var
-- reflSub {Γ₁ , Γ₂} = comma reflSub reflSub

-- equivSubs : ∀ {Γ Δ} → Γ ≡ Δ → Γ ⊢s Δ
-- equivSubs eqpf = equiv eqpf reflSub refl

-- commSub : ∀ {Γ₁ Γ₂} → (Γ₁ , Γ₂) ⊢s (Γ₂ , Γ₁)
-- commSub = equiv comm reflSub refl

-- assocSub : ∀ {Γ₁ Γ₂ Γ₃} → (Γ₁ , (Γ₂ , Γ₃)) ⊢s ((Γ₁ , Γ₂) , Γ₃)
-- assocSub = equiv assoc reflSub refl

-- symSub : ∀ {Γ Δ} → Γ ⊢s Δ → Δ ⊢s Γ
-- symSub emptySub = emptySub
-- symSub var = var
-- symSub (comma sub sub₁) = comma (symSub sub) (symSub sub₁)
-- symSub (equiv x sub x₁) = equiv (sym x₁) (symSub sub) (sym x)

-- transSub : ∀ {Γ₁ Γ₂ Γ₃} → Γ₁ ⊢s Γ₂ → Γ₂ ⊢s Γ₃ → Γ₁ ⊢s Γ₃
-- transSub sub1 sub2 = equivSubs (trans (subEquivs sub1) (subEquivs sub2))

-- congSub : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} → Γ₁ ⊢s Δ₁ → Γ₂ ⊢s Δ₂ → (Γ₁ , Γ₂) ⊢s (Δ₁ , Δ₂)
-- congSub sub1 sub2 = comma sub1 sub2

-- unitLsub : ∀ {Γ} → (· , Γ) ⊢s Γ
-- unitLsub = equiv unitL reflSub refl

-- unitRsub : ∀ {Γ} → (Γ , ·) ⊢s Γ
-- unitRsub = equiv unitR reflSub refl

-- subLemma : ∀ {Γ Γ' Δ' A} → Γ decTo sCtx A and Γ'
--                          → Δ' ⊢s Γ'
--                          → Σ[ Δ ∈ Ctx ] (Δ decTo sCtx A and Δ' × Δ ⊢s Γ)
-- subLemma (SD x) emptySub = _ , ((SD x) , var)
-- subLemma (SD ()) var
-- subLemma (SD (mulE x x₁)) (comma sub sub₁) = _ , ((SD (mulE (emptySubLemma sub x) (emptySubLemma sub₁ x₁))) , var)
-- subLemma (MD1 dec) (comma sub sub₁) with subLemma dec sub
-- ... | Δ , dec2 , sub2 = _ , ((MD1 dec2) , comma sub2 sub₁)
-- subLemma (MD2 dec) (comma sub sub₁) with subLemma dec sub₁
-- ... | Δ , dec2 , sub2 = _ , (MD2 dec2 , comma sub sub2)
-- subLemma dec (equiv x₁ sub x₂) = {!!}

-- {-# NON_TERMINATING #-}
-- dan : (Γ Γ' Γ₁' Γ₂' : Ctx) → Γ ⊢s Γ' → Γ' ≡ (Γ₁' , Γ₂') → Σ[ Γ₁ ∈ Ctx ] Σ[ Γ₂ ∈ Ctx ] ((Γ₁ , Γ₂) ≡ Γ × Γ₁ ⊢s Γ₁' × Γ₂ ⊢s Γ₂')
-- dan .· .· Γ₁' Γ₂' emptySub (emp x (mulE x₁ x₂)) = · , · , emp (mulE x x) x , equiv (emp x x) emptySub (emp x x₁) , equiv (emp x x) emptySub (emp x x₂)
-- dan .· .· Γ₁' Γ₂' emptySub (decom () x₁ pf)
-- dan ._ ._ Γ₁' Γ₂' var (emp () x₁)
-- dan ._ ._ Γ₁' Γ₂' (var {A}) (decom (SD em) (MD1 x₁) eq) = sCtx A , · , decom (MD1 (SD sinE)) (SD sinE) (emp (mulE sinE sinE) sinE) , equiv refl var (sym (lemmaSingleEmpty x₁ (fst (emptyEquiv (trans (emptyLemma em) eq))))) , equiv (emp sinE sinE) emptySub (snd (emptyEquiv (trans (emptyLemma em) eq)))
-- dan ._ ._ Γ₁' Γ₂' (var {A}) (decom (SD em) (MD2 x₁) eq) = · , sCtx A , decom (MD2 (SD sinE)) (SD sinE) (emp (mulE sinE sinE) sinE) , equiv (emp sinE sinE) emptySub (fst (emptyEquiv (trans (emptyLemma em) eq))) , equiv refl var (sym (lemmaSingleEmpty x₁ (snd (emptyEquiv (trans (emptyLemma em) eq)))))
-- dan Γ Γ' Γ₁' Γ₂' (equiv x sub x₁) pf with dan _ _ _ _ sub (trans x₁ pf)
-- ... | Γ1 , Γ2 , split , sub1 , sub2 = Γ1 , Γ2 , trans split (sym x) , sub1 , sub2
-- dan ._ ._ Γ₁' Γ₂' (comma sub sub₁) (emp (mulE x x₁) (mulE x₂ x₃)) = · , · , emp (mulE sinE sinE) (mulE (emptySubLemma sub x) (emptySubLemma sub₁ x₁)) , equiv (emp sinE sinE) emptySub (emp sinE x₂) , equiv (emp sinE sinE) emptySub (emp sinE x₃)
-- dan .(Γ₁ , Γ₂) .(Δ₁ , Δ₂) Γ₁' Γ₂' (comma {Γ₁}{Γ₂}{Δ₁}{Δ₂} sub1 sub2) (decom (MD1 {A}{Δ1} dec1) (MD1 {.A}{Γ1} dec2) pf) with equivSubs pf
-- dan _ _ Γ₁'' Γ₂' (comma sub1 sub2) (decom (MD1 dec1) (MD1 dec2) pf) | comma sub3 sub4 with subLemma dec2 sub3
-- ... | Δ , dec3 , sub5 = _ , _ , cong (decom dec3 {!!} refl) (sym (subEquivs sub2)) , sub5 , sub4
-- dan _ _ Γ₁''' Γ₂' (comma sub1 sub2) (decom (MD1 dec1) (MD1 dec2) pf) | equiv x sub3 x₁ with dan _ _ _ _ sub3 x₁
-- ... | Γ1 , Γ2 , eqpf , sub5 , sub6 = {!!} , {!!} , {!!} , {!!} , sub6
-- dan _ _ Γ₁ Γ₂' (comma sub1 sub2) (decom (MD1 dec1) (MD2 dec2) pf) = {!!}
-- dan _ _ Γ₁' Γ₂ (comma sub1 sub2) (decom (MD2 dec1) (MD1 dec2) pf) = {!!}
-- dan _ _ Γ₁ Γ₂' (comma sub1 sub2) (decom (MD2 dec1) (MD2 dec2) pf) = {!!}



--  --  addEmptyCtx : ∀ {Γ₁ Γ₂ Δ} → Γ₁ ≡ Δ → Γ₂ empty → (Γ₁ , Γ₂) ≡ Δ
--  --  addEmptyCtx (emp x x₁) empt = emp (mulE x empt) x₁
--  --  addEmptyCtx (decom x x₁ eqpf) empt = decom (MD1 x) x₁ (addEmptyCtx eqpf empt)

--  --  switchLemma : ∀ {Γ₁ Γ₂ Δ} → (Γ₁ , Γ₂) ≡ Δ → (Γ₂ , Γ₁) ≡ Δ
--  --  switchLemma (emp (mulE x x₁) x₂) = emp (mulE x₁ x) x₂
--  --  switchLemma (decom (MD1 x) x₁ eqpf) = decom (MD2 x) x₁ (switchLemma eqpf)
--  --  switchLemma (decom (MD2 x) x₁ eqpf) = decom (MD1 x) x₁ (switchLemma eqpf)

--  --  weirdLemma : ∀{Γ Δ A} → Γ decTo sCtx A and Δ → Δ empty → Γ ≡ sCtx A
--  --  weirdLemma (SD x) empt = decom (SD empt) (SD empt) (emp empt empt)
--  --  weirdLemma (MD1 decpf) (mulE empt empt₁) = addEmptyCtx (weirdLemma decpf empt) empt₁
--  --  weirdLemma (MD2 decpf) (mulE empt empt₁) = switchLemma (addEmptyCtx (weirdLemma decpf empt₁) empt)

--  --  decomposeToSingle : ∀ {Γ Δ A} → Γ ≡ sCtx A → Δ empty → Γ decTo sCtx A and Δ
--  --  decomposeToSingle (emp x ()) empt
--  --  decomposeToSingle (decom x (SD x₁) (emp x₂ x₃)) empt = swapEmptyCtx x x₂ empt
--  --  decomposeToSingle (decom x (SD x₁) (decom x₂ x₃ eqpf)) empt = abort (lemmaEmptyDecom x₁ x₃)
