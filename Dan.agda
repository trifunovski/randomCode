open import Preliminaries

module Dan where

data Tp : Set where
    P : Tp
    Q : Tp

data Ctx : Set where
    · : Ctx
    sCtx : Tp → Ctx
    _,_ : Ctx → Ctx → Ctx

mutual
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

 -- {-# NO_TERMINATION_CHECK #-}
  refl : ∀{Γ} → Γ ≡ Γ
  refl = {!!}
  -- refl {Γ} with eitherLemma Γ
  -- refl {Γ} | Inl x = emp x x
  -- refl {Γ} | Inr (a , Γ' , pf) = decom pf pf (refl {Γ'})

  comm : ∀{Γ₁ Γ₂} → (Γ₁ , Γ₂) ≡ (Γ₂ , Γ₁)
  comm = {!!}
  -- comm {Γ₁}{Γ₂} with eitherLemma Γ₁
  -- comm | Inr (A , Γ₁' , pf) = decom (MD1 pf) (MD2 pf) comm
  -- comm {Γ₁}{Γ₂} | Inl x₁ with eitherLemma Γ₂
  -- ... | Inl x = emp (mulE x₁ x) (mulE x x₁)
  -- ... | Inr (A , Γ₂' , pf) = decom (MD2 pf) (MD1 pf) comm

  assoc : ∀{Γ₁ Γ₂ Γ₃} → (Γ₁ , (Γ₂ , Γ₃)) ≡ ((Γ₁ , Γ₂) , Γ₃)
  assoc = {!!}
  -- assoc {Γ₁}{Γ₂}{Γ₃} with eitherLemma Γ₁
  -- assoc | Inr (A , Γ₁' , pf) = decom (MD1 pf) (MD1 (MD1 pf)) assoc
  -- assoc {Γ₁}{Γ₂}{Γ₃} | Inl x with eitherLemma Γ₂
  -- assoc | Inl x₁ | Inr (A , Γ₂' , pf) = decom (MD2 (MD1 pf)) (MD1 (MD2 pf)) assoc
  -- assoc {Γ₁}{Γ₂}{Γ₃} | Inl x₁ | Inl x with eitherLemma Γ₃
  -- assoc | Inl x₂ | Inl x₁ | Inr (A , Γ₃' , pf) = decom (MD2 (MD2 pf)) (MD2 pf) assoc
  -- assoc | Inl x₂ | Inl x₁ | Inl x = emp (mulE x₂ (mulE x₁ x)) (mulE (mulE x₂ x₁) x)

  sym : ∀{Γ₁ Γ₂} → Γ₁ ≡ Γ₂ → Γ₂ ≡ Γ₁
  sym (emp x x₁) = emp x₁ x
  sym (decom x x₁ pf) = decom x₁ x (sym pf)

  trans : ∀{Γ₁ Γ₂ Γ₃} → Γ₁ ≡ Γ₂ → Γ₂ ≡ Γ₃ → Γ₁ ≡ Γ₃
  trans (emp x x₁) (emp x₂ x₃) = emp x x₃
  trans (emp x x₁) (decom x₂ x₃ pf2) = abort (lemmaEmptyDecom x₁ x₂)
  trans (decom x x₁ pf1) (emp x₂ x₃) = abort (lemmaEmptyDecom x₂ x₁)
  trans (decom x x₁ pf1) (decom x₂ x₃ pf2) = {!!} --decom x (specificLemma x₁ x₂ (decProp1 x₃ (sym pf2))) pf1

  unitL : ∀ {Γ} → (· , Γ) ≡ Γ
  unitL {·} = emp (mulE sinE sinE) sinE
  unitL {sCtx x} = decom (MD2 (SD sinE)) (SD sinE) (emp (mulE sinE sinE) sinE)
  unitL {Γ₁ , Γ₂} = trans assoc (cong (unitL {Γ₁}) (refl {Γ₂}))

  unitR : ∀ {Γ} → (Γ , ·) ≡ Γ
  unitR {·} = emp (mulE sinE sinE) sinE
  unitR {sCtx x} = decom (MD1 (SD sinE)) (SD sinE) (emp (mulE sinE sinE) sinE)
  unitR {Γ₁ , Γ₂} = trans (sym assoc) (cong (refl {Γ₁}) (unitR {Γ₂}))

  cong : ∀{Γ Γ' Δ Δ'} → Γ ≡ Δ → Γ' ≡ Δ' → (Γ , Γ') ≡ (Δ , Δ')
  cong (emp x x₁) (emp x₂ x₃) = emp (mulE x x₂) (mulE x₁ x₃)
  cong (emp x x₁) (decom x₂ x₃ pf2) = decom (MD2 x₂) (MD2 x₃) (cong (emp x x₁) pf2)
  cong (decom x x₁ pf1) (emp x₂ x₃) = decom (MD1 x) (MD1 x₁) (cong pf1 (emp x₂ x₃))
  cong (decom x x₁ pf1) (decom x₂ x₃ pf2) = decom (MD1 x) (MD1 x₁) (cong pf1 (decom x₂ x₃ pf2))



  decProp : ∀{Γ Γ' A Δ} → Γ decTo sCtx A and Δ → Γ ≡ Γ' → Σ[ Δ' ∈ Ctx ] (Γ' decTo sCtx A and Δ' × Δ ≡ Δ')
  decProp (SD x) (emp () x₂)
  decProp (SD x) (decom {Δ' = Δ'} (SD x₁) x₂ eqpf) = Δ' , (x₂ , (emp x (lemma x₁ eqpf)))
  decProp (MD1 decpf) (emp (mulE x x₁) x₂) = abort (lemmaEmptyDecom x decpf)
  decProp {Γ = (Γ₁ , Γ₂)}{Γ' = Γ'}{A = A}{Δ = (Γ₁' , .Γ₂)} (MD1 decpf) (decom x x₁ eqpf) = {!!}
  decProp (MD2 decpf) (emp (mulE x x₁) x₂) = abort (lemmaEmptyDecom x₁ decpf)
  decProp (MD2 decpf) (decom x x₁ eqpf) = {!!}

  decProp0a : ∀{Γ A Δ} → Γ decTo sCtx A and Δ → Γ ≡ (sCtx A , Δ)
  decProp0a (SD x) = decom (SD x) (MD1 (SD x)) (emp x (mulE x x))
  decProp0a (MD1 decpf) = {!!} --trans (cong (decProp0a decpf) refl) (sym assoc)
  decProp0a (MD2 decpf) = {!!} --trans (trans (cong (refl) (trans (decProp0a decpf) comm)) assoc) comm

  decProp1 : ∀{Γ A Δ₁ Δ₂} → Γ decTo sCtx A and Δ₁ → Δ₁ ≡ Δ₂ → Γ decTo sCtx A and Δ₂
  decProp1 {·} () eqpf
  decProp1 {sCtx A} (SD x) eqpf = SD (lemma x eqpf)
  decProp1 {Γ₁ , Γ₂} {A} {Δ₂ = Δ₂} (MD1 {Γ₁' = Γ₁'} decpf) (emp (mulE x x₁) x₂) = decomposeToSingle (addEmptyCtx (weirdLemma decpf x) x₁) x₂
  decProp1 {Γ₁ , Γ₂} (MD1 decpf) (decom x x₁ eqpf) = {!!}
  decProp1 {Γ₁ , Γ₂} {A} {Δ₂ = Δ₂} (MD2 {Γ₂' = Γ₂'} decpf) (emp (mulE x x₁) x₂) = decomposeToSingle (switchLemma (addEmptyCtx (weirdLemma decpf x₁) x)) x₂
  decProp1 {Γ₁ , Γ₂} (MD2 decpf) (decom x x₁ eqpf) = {!!}
  
  decProp2 : ∀{Γ₁ Γ₂ A Δ} → Γ₁ decTo sCtx A and Δ → Γ₁ ≡ Γ₂ → Γ₂ decTo sCtx A and Δ
  decProp2 (SD x) (emp () x₂)
  decProp2 (SD x) (decom (SD x₁) x₂ eqpf) = {!!}
  decProp2 (MD1 decpf) (emp (mulE x x₁) x₂) = abort (lemmaEmptyDecom x decpf)
  decProp2 (MD1 decpf) (decom x x₁ eqpf) = {!!}
  decProp2 (MD2 decpf) (emp (mulE x x₁) x₂) = abort (lemmaEmptyDecom x₁ decpf)
  decProp2 (MD2 decpf) (decom x x₁ eqpf) = {!!}

  decProp3 : ∀{Γ A B Δ} → Γ decTo sCtx A and Δ → Γ decTo sCtx B and Δ → sCtx A ≡ sCtx B
  decProp3 (SD x) (SD x₁) = decom (SD x₁) (SD x₁) (emp x₁ x₁)
  decProp3 (MD1 dec1) (MD1 dec2) = decProp3 dec1 dec2
  decProp3 (MD1 dec1) (MD2 dec2) = abort (decError dec2)
  decProp3 (MD2 dec1) (MD1 dec2) = abort (decError dec2)
  decProp3 (MD2 dec1) (MD2 dec2) = decProp3 dec1 dec2

  decError : ∀ {Γ A} → Γ decTo sCtx A and Γ → Void
  decError (SD ())
  decError (MD1 dec) = decError dec
  decError (MD2 dec) = decError dec

  decProp4 : ∀{Γ A Δ₁ Δ₂} → Γ decTo sCtx A and Δ₁ → Γ decTo sCtx A and Δ₂ → Δ₁ ≡ Δ₂
  decProp4 (SD x) (SD x₁) = emp x x₁
  decProp4 (MD1 dec1) (MD1 dec2) = cong (decProp4 dec1 dec2) refl
  decProp4 (MD1 dec1) (MD2 dec2) = {!!}
  decProp4 (MD2 dec1) (MD1 dec2) = {!!}
  decProp4 (MD2 dec1) (MD2 dec2) = cong refl (decProp4 dec1 dec2)

  decProp5 : ∀{Γ₁ Γ₂ A Δ} → Γ₁ decTo sCtx A and Δ → Γ₂ decTo sCtx A and Δ → Γ₁ ≡ Γ₂
  decProp5 (SD x) (SD x₁) = decom (SD x₁) (SD x₁) (emp x₁ x₁)
  decProp5 (SD x) (MD1 dec2) = decom (SD x) (MD1 dec2) (emp x x)
  decProp5 (SD x) (MD2 dec2) = decom (SD x) (MD2 dec2) (emp x x)
  decProp5 (MD1 dec1) (SD x) = decom (MD1 dec1) (SD x) (emp x x)
  decProp5 (MD1 dec1) (MD1 dec2) = cong (decProp5 dec1 dec2) refl
  decProp5 (MD1 dec1) (MD2 dec2) = {!!}
  decProp5 (MD2 dec1) (SD x) = decom (MD2 dec1) (SD x) (emp x x)
  decProp5 (MD2 dec1) (MD1 dec2) = {!!}
  decProp5 (MD2 dec1) (MD2 dec2) = cong refl (decProp5 dec1 dec2)



  lemma : ∀{Γ Δ} → Γ empty → Γ ≡ Δ → Δ empty
  lemma sinE (emp x x₁) = x₁
  lemma sinE (decom x x₁ pf) = abort (lemmaEmptyDecom sinE x)
  lemma (mulE empt empt₁) (emp x x₁) = x₁
  lemma (mulE {Γ₁}{Γ₂} empt empt₁) (decom x x₁ pf) = abort (lemmaEmptyDecom (mulE empt empt₁) x)

  lemmaEmptyDecom : ∀{Γ A Δ} → Γ empty → Γ decTo sCtx A and Δ → Void
  lemmaEmptyDecom sinE ()
  lemmaEmptyDecom (mulE empt empt₁) (MD1 decpf) = lemmaEmptyDecom empt decpf
  lemmaEmptyDecom (mulE empt empt₁) (MD2 decpf) = lemmaEmptyDecom empt₁ decpf

  eitherLemma : (Γ : Ctx) → Either (Γ empty) (Σ[ A ∈ Tp ] Σ[ Γ' ∈ Ctx ] (Γ decTo sCtx A and Γ'))
  eitherLemma · = Inl sinE
  eitherLemma (sCtx x) = Inr (x , (· , SD sinE))
  eitherLemma (Γ₁ , Γ₂) with eitherLemma Γ₁
  eitherLemma (Γ₁ , Γ₂) | Inr (a , Γ' , pf) = Inr (a , ((Γ' , Γ₂) , MD1 pf))
  eitherLemma (Γ₁ , Γ₂) | Inl x with eitherLemma Γ₂
  eitherLemma (Γ₁ , Γ₂) | Inl x₁ | Inl x = Inl (mulE x₁ x)
  eitherLemma (Γ₁ , Γ₂) | Inl x₁ | Inr (a , Γ' , pf) = Inr (a , ((Γ₁ , Γ') , MD2 pf))

  emptyEquiv : ∀ {Γ₁ Γ₂} → · ≡ (Γ₁ , Γ₂) → · ≡ Γ₁ × · ≡ Γ₂
  emptyEquiv (emp x (mulE x₁ x₂)) = emp x x₁ , emp x x₂
  emptyEquiv (decom () x₁ pf)

  addEmptyCtx : ∀ {Γ₁ Γ₂ Δ} → Γ₁ ≡ Δ → Γ₂ empty → (Γ₁ , Γ₂) ≡ Δ
  addEmptyCtx (emp x x₁) empt = emp (mulE x empt) x₁
  addEmptyCtx (decom x x₁ eqpf) empt = decom (MD1 x) x₁ (addEmptyCtx eqpf empt)

  switchLemma : ∀ {Γ₁ Γ₂ Δ} → (Γ₁ , Γ₂) ≡ Δ → (Γ₂ , Γ₁) ≡ Δ
  switchLemma (emp (mulE x x₁) x₂) = emp (mulE x₁ x) x₂
  switchLemma (decom (MD1 x) x₁ eqpf) = decom (MD2 x) x₁ (switchLemma eqpf)
  switchLemma (decom (MD2 x) x₁ eqpf) = decom (MD1 x) x₁ (switchLemma eqpf)

  weirdLemma : ∀{Γ Δ A} → Γ decTo sCtx A and Δ → Δ empty → Γ ≡ sCtx A
  weirdLemma (SD x) empt = decom (SD empt) (SD empt) (emp empt empt)
  weirdLemma (MD1 decpf) (mulE empt empt₁) = addEmptyCtx (weirdLemma decpf empt) empt₁
  weirdLemma (MD2 decpf) (mulE empt empt₁) = switchLemma (addEmptyCtx (weirdLemma decpf empt₁) empt)

  swapEmptyCtx : ∀{Γ A Δ₁ Δ₂} → Γ decTo sCtx A and Δ₁ → Δ₁ empty → Δ₂ empty → Γ decTo sCtx A and Δ₂
  swapEmptyCtx (SD x) emp1 emp2 = SD emp2
  swapEmptyCtx (MD1 decpf) (mulE emp1 emp2) emp3 = decProp2 (swapEmptyCtx decpf emp1 emp3) (sym (addEmptyCtx refl emp2))
  swapEmptyCtx (MD2 decpf) (mulE emp1 emp2) emp3 = decProp2 (swapEmptyCtx decpf emp2 emp3) (sym (switchLemma (addEmptyCtx refl emp1)))

  decomposeToSingle : ∀ {Γ Δ A} → Γ ≡ sCtx A → Δ empty → Γ decTo sCtx A and Δ
  decomposeToSingle (emp x ()) empt
  decomposeToSingle (decom x (SD x₁) (emp x₂ x₃)) empt = swapEmptyCtx x x₂ empt
  decomposeToSingle (decom x (SD x₁) (decom x₂ x₃ eqpf)) empt = abort (lemmaEmptyDecom x₁ x₃)
  

  specificLemma : ∀ {Γ Γ' Δ Δ' A B} → Γ decTo sCtx A and Δ
                                    → Γ decTo sCtx B and Δ'
                                    → Γ' decTo sCtx B and Δ'
                                    → Γ' decTo sCtx A and Δ
  specificLemma dec1 (SD x) (SD x₁) = dec1
  specificLemma (SD x) (SD (mulE x₁ x₂)) dec3 = decProp1 dec3 (emp (mulE x₁ x₂) x)
  specificLemma (MD1 dec1) (MD1 dec2) (SD (mulE x x₁)) = {!!}
  specificLemma (MD2 dec1) (MD1 dec2) (SD (mulE x x₁)) = {!!}
  specificLemma (MD1 dec1) (MD2 dec2) (SD (mulE x x₁)) = {!!}
  specificLemma (MD2 dec1) (MD2 dec2) (SD (mulE x x₁)) = {!!}
  specificLemma (MD2 dec1) (MD1 dec2) (MD1 dec3) = {!!}
  specificLemma (MD1 dec1) (MD1 dec2) (MD2 dec3) = {!!}
  specificLemma (MD2 dec1) (MD1 dec2) (MD2 dec3) = {!!}
  specificLemma (MD1 dec1) (MD2 dec2) (MD1 dec3) = {!!}
  specificLemma (MD2 dec1) (MD2 dec2) (MD1 dec3) = {!!}
  specificLemma (MD1 dec1) (MD2 dec2) (MD2 dec3) = {!!}
  specificLemma (MD1 dec1) (MD1 dec2) (MD1 dec3) = MD1 (specificLemma dec1 dec2 dec3)
  specificLemma (MD2 dec1) (MD2 dec2) (MD2 dec3) = MD2 (specificLemma dec1 dec2 dec3)

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

  subEqLemma : ∀{Γ Δ Δ'} → Γ ⊢s Δ → Δ ≡ Δ' → Γ ⊢s Δ'
  subEqLemma emptySub (emp x x₁) = equiv (emp x x) emptySub (emp x x₁)
  subEqLemma emptySub (decom x x₁ eq) = equiv (emp sinE sinE) emptySub (decom x x₁ eq)
  subEqLemma var (emp x x₁) = equiv (emp x x) var (emp x x₁)
  subEqLemma var (decom x x₁ eq) = equiv (decom (SD sinE) (SD sinE) (emp sinE sinE)) var
                                     (decom x x₁ eq)
  subEqLemma (comma sub sub₁) (emp (mulE x x₁) x₂) = equiv refl (comma (subEqLemma sub (sym (emptyLemma x))) (subEqLemma sub₁ (sym (emptyLemma x₁)))) (emp (mulE sinE sinE) x₂)
  subEqLemma (comma sub sub₁) (decom (MD1 x) x₁ eq) = {!!}
  subEqLemma (comma sub sub₁) (decom (MD2 x) x₁ eq) = {!!}
  subEqLemma (equiv x sub x₁) decpf = equiv x (subEqLemma sub x₁) decpf

  subDecLemma : ∀{Γ₁ A Δ₁ Δ₂} → Γ₁ ⊢s Δ₁ → Δ₁ decTo sCtx A and Δ₂ → Σ[ B ∈ Tp ] Σ[ Γ₂ ∈ Ctx ] ((Γ₁ decTo sCtx B and Γ₂) × sCtx A ⊢s sCtx B × Δ₂ ⊢s Γ₂)
  subDecLemma emptySub ()
  subDecLemma {A = A} var (SD x) = A , (· , (SD sinE , (var , equiv (emp x sinE) emptySub (emp sinE sinE))))
  subDecLemma (comma sub sub₁) (MD1 decpf) = {!!}
  subDecLemma (comma sub sub₁) (MD2 decpf) = {!!}
  subDecLemma (equiv x sub x₁) (SD x₂) = {!!}
  subDecLemma (equiv x sub x₁) (MD1 decpf) = {!!}
  subDecLemma (equiv x sub x₁) (MD2 decpf) = {!!}

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
 -- dan .(Γ₁ , Γ₂) .(Δ₁ , Δ₂) Γ₁' Γ₂' (comma {Γ₁}{Γ₂}{Δ₁}{Δ₂} sub1 sub2) (decom {Γ' = Γ'}{Δ' = Δ'}{A = A} dec1 dec2 pf) = {!!}
 -- dan .(Γ₁ , Γ₂) .(Δ₁ , Δ₂) Γ₁' Γ₂' (comma {Γ₁}{Γ₂}{Δ₁}{Δ₂} sub1 sub2) (decom (MD1 {A}{Δ1} dec1) (MD1 {.A}{Γ1} dec2) pf) = {!!}




  test : ∀ {Γ} → ((· , (· , Γ)) , ·) ≡ Γ
  test {Γ} = trans unitR (trans unitL unitL)


