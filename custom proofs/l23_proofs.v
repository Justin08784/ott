Lemma PSZ_to_Z : red (TmPred (TmSucc TmZero)) TmZero.
Proof.
  eapply E_PredSucc.
  simpl. reflexivity.
Qed.

Lemma PSSZ_to_SZ : red (TmPred (TmSucc (TmSucc TmZero))) (TmSucc TmZero).
Proof.
  eapply E_PredSucc.
  simpl. reflexivity.
Qed.


Lemma PPZ_to_PZ : red (TmPred (TmPred TmZero)) (TmPred TmZero).
Proof.
  (* Prove the inner reduction: TmPred TmZero reduces to TmZero *)
  assert (red (TmPred TmZero) TmZero) as RedInner.
  {
    (* Apply the appropriate reduction rule *)
    apply E_PredZero.
  }

  (* Apply E_Pred with the proved reduction *)
  apply E_Pred in RedInner.

  simpl.
  (* Now you have the desired reduction *)
  exact RedInner.
  (* ...alternatively to 'exact RedInner' *)
  (* assumption. *)
  (* auto. *)
  (* apply RedInner. *)

Qed.

Lemma PPZ_bigstep_Z : redB (TmPred (TmPred TmZero)) TmZero.
Proof.
  assert (redB TmZero TmZero) as RedInner1.
  {
    (* Apply the appropriate reduction rule *)
    apply EB_Val.
    simpl. reflexivity.
  }
  
  (* Prove the inner reduction: TmPred TmZero reduces to TmZero *)
  assert (redB (TmPred TmZero) TmZero) as RedInner2.
  {
    (* Apply the appropriate reduction rule *)
    apply EB_PredZero in RedInner1.
    assumption.
  }

  apply EB_PredZero in RedInner2.
  assumption.
  (* trivial. *)
Qed.


Lemma iseven_example : red (TmIseven (TmSucc (TmZero))) (TmNot (TmIseven TmZero)).
Proof.
  (* Prove the inner reduction: TmPred TmZero reduces to TmZero *)
  eapply E_IsEvenSucc.
  simpl. reflexivity.
Qed.



Lemma PSPZ_to_Z : redB (TmPred (TmSucc (TmPred TmZero))) TmZero.
Proof.
  assert (redB TmZero TmZero) as Z_to_Z.
  {
    (* Apply the appropriate reduction rule *)
    apply EB_Val.
    simpl. reflexivity.
  }
  apply EB_PredZero in Z_to_Z as PZ_to_Z.
  apply EB_Succ in PZ_to_Z as SPZ_to_SZ.
  apply EB_PredSucc in SPZ_to_SZ as RV.


  apply RV.

  simpl. reflexivity.
  simpl. reflexivity.
Qed.


Lemma ExCondTrue : redB (TmCond TmTrue (TmSucc TmZero) TmZero) (TmSucc TmZero).
Proof.
  (* Prove the inner reduction: TmPred TmZero reduces to TmZero *)
  eapply EB_CondTrue.
  simpl. 
  
  assert (redB TmTrue TmTrue ) as T_to_T.
  {
    (* Apply the appropriate reduction rule *)
    apply EB_Val.
    simpl. reflexivity.
  }
  apply T_to_T.
Qed.


Lemma ExCondFalse : redB (TmCond TmFalse (TmSucc TmZero) TmZero) TmZero.
Proof.
  (* Prove the inner reduction: TmPred TmZero reduces to TmZero *)
  eapply EB_CondFalse.
  simpl. 
  
  assert (redB TmFalse TmFalse) as F_to_F.
  {
    (* Apply the appropriate reduction rule *)
    apply EB_Val.
    simpl. reflexivity.
  }
  apply F_to_F.
Qed.








Lemma ExTypTrue : (typing TmTrue TyBool).
Proof.
    apply T_True.
Qed.

Theorem ExTypCond : (typing (TmCond TmTrue (TmSucc TmZero) TmZero) TyNat).
Proof.
    assert (typing TmZero TyNat) as zero_nat.
    {
        apply T_Zero.
    }    

    assert (typing (TmSucc TmZero) TyNat) as one_nat.
    {
        apply T_Succ in zero_nat.
        assumption.
    }

    assert (typing TmTrue TyBool) as true_bool.
    {
        apply ExTypTrue.
    }

    apply T_Cond.
    - exact true_bool.
    - exact one_nat.
    - exact zero_nat.
Qed.


Lemma ExRecord : redB (TmRecordGet (TmRecord ((1, TmPred TmZero)::nil)) 1) TmZero.
Proof.
  (* Prove the inner reduction: TmPred TmZero reduces to TmZero *)
  assert ( redB (TmPred TmZero) TmZero) as one.
  {
    apply EB_PredZero.
    apply EB_Val.
    simpl. reflexivity.
  }
  (* now what??? *)
Qed.