open import Preliminaries

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


eitherLemma : (Γ : Ctx) → Either (Γ empty) (Σ[ A ∈ Tp ] Σ[ Γ' ∈ Ctx ] (Γ decTo sCtx A and Γ'))
eitherLemma · = Inl sinE
eitherLemma (sCtx x) = Inr (x , (· , SD sinE))
eitherLemma (Γ₁ , Γ₂) with eitherLemma Γ₁
eitherLemma (Γ₁ , Γ₂) | Inr (a , Γ' , pf) = Inr (a , ((Γ' , Γ₂) , MD1 pf))
eitherLemma (Γ₁ , Γ₂) | Inl x with eitherLemma Γ₂
eitherLemma (Γ₁ , Γ₂) | Inl x₁ | Inl x = Inl (mulE x₁ x)
eitherLemma (Γ₁ , Γ₂) | Inl x₁ | Inr (a , Γ' , pf) = Inr (a , ((Γ₁ , Γ') , MD2 pf))

lemmaEmptyDecom : ∀{Γ A Δ} → Γ empty → Γ decTo sCtx A and Δ → Void
lemmaEmptyDecom sinE ()
lemmaEmptyDecom (mulE empt empt₁) (MD1 decpf) = lemmaEmptyDecom empt decpf
lemmaEmptyDecom (mulE empt empt₁) (MD2 decpf) = lemmaEmptyDecom empt₁ decpf

lemma : ∀{Γ Δ} → Γ empty → Γ ≡ Δ → Δ empty
lemma sinE (emp x x₁) = x₁
lemma sinE (decom x x₁ pf) = abort (lemmaEmptyDecom sinE x)
lemma (mulE empt empt₁) (emp x x₁) = x₁
lemma (mulE {Γ₁}{Γ₂} empt empt₁) (decom x x₁ pf) = abort (lemmaEmptyDecom (mulE empt empt₁) x)


{-# NON_TERMINATING #-}
refl : ∀{Γ} → Γ ≡ Γ
refl {Γ} with eitherLemma Γ
refl {Γ} | Inl x = emp x x
refl {Γ} | Inr (a , Γ' , pf) = decom pf pf (refl {Γ'})

{-# NON_TERMINATING #-}
comm : ∀{Γ₁ Γ₂} → (Γ₁ , Γ₂) ≡ (Γ₂ , Γ₁)
comm {Γ₁}{Γ₂} with eitherLemma Γ₁
comm | Inr (A , Γ₁' , pf) = decom (MD1 pf) (MD2 pf) comm
comm {Γ₁}{Γ₂} | Inl x₁ with eitherLemma Γ₂
... | Inl x = emp (mulE x₁ x) (mulE x x₁)
... | Inr (A , Γ₂' , pf) = decom (MD2 pf) (MD1 pf) comm

{-# NON_TERMINATING #-}
assoc : ∀{Γ₁ Γ₂ Γ₃} → (Γ₁ , (Γ₂ , Γ₃)) ≡ ((Γ₁ , Γ₂) , Γ₃)
assoc {Γ₁}{Γ₂}{Γ₃} with eitherLemma Γ₁
assoc | Inr (A , Γ₁' , pf) = decom (MD1 pf) (MD1 (MD1 pf)) assoc
assoc {Γ₁}{Γ₂}{Γ₃} | Inl x with eitherLemma Γ₂
assoc | Inl x₁ | Inr (A , Γ₂' , pf) = decom (MD2 (MD1 pf)) (MD1 (MD2 pf)) assoc
assoc {Γ₁}{Γ₂}{Γ₃} | Inl x₁ | Inl x with eitherLemma Γ₃
assoc | Inl x₂ | Inl x₁ | Inr (A , Γ₃' , pf) = decom (MD2 (MD2 pf)) (MD2 pf) assoc
assoc | Inl x₂ | Inl x₁ | Inl x = emp (mulE x₂ (mulE x₁ x)) (mulE (mulE x₂ x₁) x)

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
transHelper {Γ₁ , Γ₂} (MD1 dec1) (MD1 dec2) | Inl (decom (SD x) (SD x₁) seq , ctxeq) = Inl ((decom (SD x) (SD x₁) seq) , (cong ctxeq refl))
transHelper {Γ₁ , Γ₂} (MD1 dec1) (MD1 dec2) | Inr (Δ₁ , Δ₂ , dec3 , dec4 , eq) = Inr ((Δ₁ , Γ₂) , (Δ₂ , Γ₂) , MD1 dec3 , MD1 dec4 , cong eq refl)
transHelper {Γ₁ , Γ₂} (MD1 dec1) (MD2 dec2) = Inr (_ , _ , MD2 dec2 , MD1 dec1 , refl)
transHelper {Γ₁ , Γ₂} (MD2 dec1) (MD1 dec2) = Inr (_ , _ , MD1 dec2 , MD2 dec1 , refl)
transHelper {Γ₁ , Γ₂} (MD2 dec1) (MD2 dec2) with transHelper dec1 dec2
transHelper {Γ₁ , Γ₂} (MD2 dec1) (MD2 dec2) | Inl (emp () x₁ , ctxeq)
transHelper {Γ₁ , Γ₂} (MD2 dec1) (MD2 dec2) | Inl (decom (SD x) (SD x₁) seq , ctxeq) = Inl ((decom (SD x) (SD x₁) seq) , (cong refl ctxeq))
transHelper {Γ₁ , Γ₂} (MD2 dec1) (MD2 dec2) | Inr (Δ₁ , Δ₂ , dec3 , dec4 , eq) = Inr ((Γ₁ , Δ₁) , (Γ₁ , Δ₂) , MD2 dec3 , MD2 dec4 , cong refl eq)

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
  decProp : ∀{Γ Γ' A Δ} → Γ decTo sCtx A and Δ
                      → Γ ≡ Γ'
                      → Σ[ Δ' ∈ Ctx ] (Γ' decTo sCtx A and Δ' × Δ ≡ Δ')
  decProp (SD x) (emp () x₂)
  decProp (SD x) (decom {Δ' = Δ'} (SD x₁) x₂ eqpf) = Δ' , (x₂ , (emp x (lemma x₁ eqpf)))
  decProp (MD1 decpf) (emp (mulE x x₁) x₂) = abort (lemmaEmptyDecom x decpf)
  decProp (MD2 decpf) (emp (mulE x x₁) x₂) = abort (lemmaEmptyDecom x₁ decpf)
  decProp decpf (decom x x₁ eqpf) with transHelper decpf x
  decProp decpf (decom x x₃ eqpf) | Inl (emp () x₂ , snd)
  decProp decpf (decom x x₃ eqpf) | Inl (decom (SD x₁) (SD x₂) fst , snd) = _ , (x₃ , trans snd eqpf)
  decProp decpf (decom x x₂ eqpf) | Inr (Δ₁ , Δ₂ , dec3 , dec4 , eq2) with decProp dec4 eqpf
  ... | Δ₃ , dec5 , eq3 with transNewHelper x₂ dec5
  ... | Δ₄ , dec6 , dec7 = Δ₄ , (dec6 , decom dec3 dec7 (trans eq2 eq3))

  {-# NON_TERMINATING #-}
  trans : ∀{Γ₁ Γ₂ Γ₃} → Γ₁ ≡ Γ₂ → Γ₂ ≡ Γ₃ → Γ₁ ≡ Γ₃
  trans (emp x x₁) (emp x₂ x₃) = emp x x₃
  trans (emp x x₁) (decom x₂ x₃ pf2) = abort (lemmaEmptyDecom x₁ x₂)
  trans (decom x x₁ pf1) (emp x₂ x₃) = abort (lemmaEmptyDecom x₂ x₁)
  trans (decom x x₁ pf1) (decom x₂ x₃ pf2) with transHelper x₁ x₂
  trans (decom x₄ x₁ pf1) (decom x₂ x₅ pf2) | Inl (emp () x₃ , ctxeq)
  trans (decom x₄ x₁ pf1) (decom x₂ x₅ pf2) | Inl (decom (SD x) (SD x₃) seq , ctxeq) = decom x₄ x₅ (trans pf1 (trans ctxeq pf2))
  trans (decom x₃ x₁ pf1) (decom x₂ x₄ pf2) | Inr (Δ₁ , Δ₂ , dec1 , dec2 , eq) with decProp dec1 (sym pf1) | decProp dec2 pf2
  ... | Δ₃ , dec3 , eq3 | Δ₄ , dec4 , eq4 with transNewHelper x₄ dec4
  ... | Γ₄ , dec5 , dec6 = decom x₃ dec5 (decom dec3 dec6 (trans (sym eq3) (trans eq eq4)))

unitL : ∀ {Γ} → (· , Γ) ≡ Γ
unitL {·} = emp (mulE sinE sinE) sinE
unitL {sCtx x} = decom (MD2 (SD sinE)) (SD sinE) (emp (mulE sinE sinE) sinE)
unitL {Γ₁ , Γ₂} = trans assoc (cong (unitL {Γ₁}) (refl {Γ₂}))

unitR : ∀ {Γ} → (Γ , ·) ≡ Γ
unitR {·} = emp (mulE sinE sinE) sinE
unitR {sCtx x} = decom (MD1 (SD sinE)) (SD sinE) (emp (mulE sinE sinE) sinE)
unitR {Γ₁ , Γ₂} = trans (sym assoc) (cong (refl {Γ₁}) (unitR {Γ₂}))



emptyEquiv : ∀ {Γ₁ Γ₂} → · ≡ (Γ₁ , Γ₂) → · ≡ Γ₁ × · ≡ Γ₂
emptyEquiv (emp x (mulE x₁ x₂)) = emp x x₁ , emp x x₂
emptyEquiv (decom () x₁ pf)

emptySubLemma : ∀ {Γ Δ} → Γ ⊢s Δ → Δ empty → Γ empty
emptySubLemma emptySub empt = empt
emptySubLemma var ()
emptySubLemma (comma sub sub₁) (mulE empt empt₁) = mulE (emptySubLemma sub empt) (emptySubLemma sub₁ empt₁)
emptySubLemma (equiv x sub x₁) empt = lemma (emptySubLemma sub (lemma empt (sym x₁))) (sym x)

lemmaSingleEmpty : ∀ {Γ A Δ} → Γ decTo sCtx A and Δ → · ≡ Δ → Γ ≡ sCtx A
lemmaSingleEmpty (SD x) empteq = decom (SD x) (SD x) (emp x x)
lemmaSingleEmpty (MD1 decpf) empteq = decom (MD1 decpf) (SD sinE) (sym empteq)
lemmaSingleEmpty (MD2 decpf) empteq = decom (MD2 decpf) (SD sinE) (sym empteq)

emptyLemma : ∀ {Γ} → Γ empty → · ≡ Γ
emptyLemma sinE = emp sinE sinE
emptyLemma (mulE pf pf₁) = emp sinE (mulE pf pf₁)

subItselfLemma : ∀ {Γ} → Γ ⊢s Γ
subItselfLemma {·} = emptySub
subItselfLemma {sCtx x} = var
subItselfLemma {Γ₁ , Γ₂} = comma subItselfLemma subItselfLemma

flipSub : ∀ {Γ Δ} → Γ ⊢s Δ → Δ ⊢s Γ
flipSub emptySub = emptySub
flipSub var = var
flipSub (comma sub sub₁) = comma (flipSub sub) (flipSub sub₁)
flipSub (equiv x sub x₁) = equiv (sym x₁) (flipSub sub) (sym x)

dan : (Γ Γ' Γ₁' Γ₂' : Ctx) → Γ ⊢s Γ' → Γ' ≡ (Γ₁' , Γ₂') → Σ[ Γ₁ ∈ Ctx ] Σ[ Γ₂ ∈ Ctx ] ((Γ₁ , Γ₂) ≡ Γ × Γ₁ ⊢s Γ₁' × Γ₂ ⊢s Γ₂')
dan .· .· Γ₁' Γ₂' emptySub (emp x (mulE x₁ x₂)) = · , · , emp (mulE x x) x , equiv (emp x x) emptySub (emp x x₁) , equiv (emp x x) emptySub (emp x x₂)
dan .· .· Γ₁' Γ₂' emptySub (decom () x₁ pf)
dan ._ ._ Γ₁' Γ₂' var (emp () x₁)
dan ._ ._ Γ₁' Γ₂' (var {A}) (decom (SD em) (MD1 x₁) eq) = sCtx A , · , decom (MD1 (SD sinE)) (SD sinE) (emp (mulE sinE sinE) sinE) , equiv refl var (sym (lemmaSingleEmpty x₁ (fst (emptyEquiv (trans (emptyLemma em) eq))))) , equiv (emp sinE sinE) emptySub (snd (emptyEquiv (trans (emptyLemma em) eq)))
dan ._ ._ Γ₁' Γ₂' (var {A}) (decom (SD em) (MD2 x₁) eq) = · , sCtx A , decom (MD2 (SD sinE)) (SD sinE) (emp (mulE sinE sinE) sinE) , equiv (emp sinE sinE) emptySub (fst (emptyEquiv (trans (emptyLemma em) eq))) , equiv refl var (sym (lemmaSingleEmpty x₁ (snd (emptyEquiv (trans (emptyLemma em) eq)))))
dan Γ Γ' Γ₁' Γ₂' (equiv x sub x₁) pf with dan _ _ _ _ sub (trans x₁ pf)
... | Γ1 , Γ2 , split , sub1 , sub2 = Γ1 , Γ2 , trans split (sym x) , sub1 , sub2
dan ._ ._ Γ₁' Γ₂' (comma sub sub₁) (emp (mulE x x₁) (mulE x₂ x₃)) = · , · , emp (mulE sinE sinE) (mulE (emptySubLemma sub x) (emptySubLemma sub₁ x₁)) , equiv (emp sinE sinE) emptySub (emp sinE x₂) , equiv (emp sinE sinE) emptySub (emp sinE x₃)
dan .(Γ₁ , Γ₂) .(Δ₁ , Δ₂) Γ₁' Γ₂' (comma {Γ₁}{Γ₂}{Δ₁}{Δ₂} sub1 sub2) (decom (MD1 {A}{Δ1} dec1) (MD1 {.A}{Γ1} dec2) pf) = {!!}
dan _ _ Γ₁ Γ₂' (comma sub1 sub2) (decom (MD1 dec1) (MD2 dec2) pf) = {!!}
dan _ _ Γ₁' Γ₂ (comma sub1 sub2) (decom (MD2 dec1) (MD1 dec2) pf) = {!!}
dan _ _ Γ₁ Γ₂' (comma sub1 sub2) (decom (MD2 dec1) (MD2 dec2) pf) = {!!}



 --  addEmptyCtx : ∀ {Γ₁ Γ₂ Δ} → Γ₁ ≡ Δ → Γ₂ empty → (Γ₁ , Γ₂) ≡ Δ
 --  addEmptyCtx (emp x x₁) empt = emp (mulE x empt) x₁
 --  addEmptyCtx (decom x x₁ eqpf) empt = decom (MD1 x) x₁ (addEmptyCtx eqpf empt)

 --  switchLemma : ∀ {Γ₁ Γ₂ Δ} → (Γ₁ , Γ₂) ≡ Δ → (Γ₂ , Γ₁) ≡ Δ
 --  switchLemma (emp (mulE x x₁) x₂) = emp (mulE x₁ x) x₂
 --  switchLemma (decom (MD1 x) x₁ eqpf) = decom (MD2 x) x₁ (switchLemma eqpf)
 --  switchLemma (decom (MD2 x) x₁ eqpf) = decom (MD1 x) x₁ (switchLemma eqpf)

 --  weirdLemma : ∀{Γ Δ A} → Γ decTo sCtx A and Δ → Δ empty → Γ ≡ sCtx A
 --  weirdLemma (SD x) empt = decom (SD empt) (SD empt) (emp empt empt)
 --  weirdLemma (MD1 decpf) (mulE empt empt₁) = addEmptyCtx (weirdLemma decpf empt) empt₁
 --  weirdLemma (MD2 decpf) (mulE empt empt₁) = switchLemma (addEmptyCtx (weirdLemma decpf empt₁) empt)

 --  decomposeToSingle : ∀ {Γ Δ A} → Γ ≡ sCtx A → Δ empty → Γ decTo sCtx A and Δ
 --  decomposeToSingle (emp x ()) empt
 --  decomposeToSingle (decom x (SD x₁) (emp x₂ x₃)) empt = swapEmptyCtx x x₂ empt
 --  decomposeToSingle (decom x (SD x₁) (decom x₂ x₃ eqpf)) empt = abort (lemmaEmptyDecom x₁ x₃)
