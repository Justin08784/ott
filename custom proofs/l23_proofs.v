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


Lemma PPZ_to_PZ : red (TmIseven (TmSucc (TmZero))) (TmNot (TmIseven TmZero)).
Proof.
  (* Prove the inner reduction: TmPred TmZero reduces to TmZero *)
  eapply E_IsEvenSucc.
  simpl. reflexivity.
Qed.
