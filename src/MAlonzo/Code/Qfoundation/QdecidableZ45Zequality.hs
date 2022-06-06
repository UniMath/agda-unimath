{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QdecidableZ45Zequality where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.QfibersZ45ZofZ45Zmaps
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qpropositions
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qretractions
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qsets
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtypeZ45ZarithmeticZ45ZdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QdecidableZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QequalityZ45ZdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.Qpropositions
import qualified MAlonzo.Code.Qfoundation.Qsections
import qualified MAlonzo.Code.Qfoundation.QunitZ45Ztype

-- foundation.decidable-equality.has-decidable-equality
d_has'45'decidable'45'equality_8 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> ()
d_has'45'decidable'45'equality_8 = erased
-- foundation.decidable-equality.has-decidable-equality-is-prop
d_has'45'decidable'45'equality'45'is'45'prop_20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_has'45'decidable'45'equality'45'is'45'prop_20 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_has'45'decidable'45'equality'45'is'45'prop_20
du_has'45'decidable'45'equality'45'is'45'prop_20 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_has'45'decidable'45'equality'45'is'45'prop_20
  = coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 erased
-- foundation.decidable-equality.has-decidable-equality-empty
d_has'45'decidable'45'equality'45'empty_28 ::
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_has'45'decidable'45'equality'45'empty_28 ~v0
  = du_has'45'decidable'45'equality'45'empty_28
du_has'45'decidable'45'equality'45'empty_28 ::
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_has'45'decidable'45'equality'45'empty_28
  = MAlonzo.RTE.mazUnreachableError
-- foundation.decidable-equality.has-decidable-equality-unit
d_has'45'decidable'45'equality'45'unit_30 ::
  MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4 ->
  MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_has'45'decidable'45'equality'45'unit_30 ~v0 ~v1
  = du_has'45'decidable'45'equality'45'unit_30
du_has'45'decidable'45'equality'45'unit_30 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_has'45'decidable'45'equality'45'unit_30
  = coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 erased
-- foundation.decidable-equality.has-decidable-equality-prod'
d_has'45'decidable'45'equality'45'prod''_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_has'45'decidable'45'equality'45'prod''_44 ~v0 ~v1 ~v2 ~v3 v4 v5
                                            v6 v7
  = du_has'45'decidable'45'equality'45'prod''_44 v4 v5 v6 v7
du_has'45'decidable'45'equality'45'prod''_44 ::
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_has'45'decidable'45'equality'45'prod''_44 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v4 v5
        -> case coe v3 of
             MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v6 v7
               -> let v8 = coe v0 v5 v4 v6 in
                  let v9 = coe v1 v4 v5 v7 in
                  case coe v8 of
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v10
                      -> case coe v9 of
                           MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v11
                             -> coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 erased
                           MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v11
                             -> coe
                                  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                                  (coe (\ v12 -> coe v11 erased))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v10
                      -> coe
                           seq (coe v9)
                           (coe
                              MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                              (coe (\ v11 -> coe v10 erased)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.decidable-equality.has-decidable-equality-prod
d_has'45'decidable'45'equality'45'prod_132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_has'45'decidable'45'equality'45'prod_132 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_has'45'decidable'45'equality'45'prod_132 v4 v5
du_has'45'decidable'45'equality'45'prod_132 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_has'45'decidable'45'equality'45'prod_132 v0 v1
  = coe
      du_has'45'decidable'45'equality'45'prod''_44 (coe (\ v2 -> v0))
      (coe (\ v2 -> v1))
-- foundation.decidable-equality.has-decidable-equality-left-factor
d_has'45'decidable'45'equality'45'left'45'factor_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_has'45'decidable'45'equality'45'left'45'factor_150 ~v0 ~v1 ~v2
                                                     ~v3 v4 v5 v6 v7
  = du_has'45'decidable'45'equality'45'left'45'factor_150 v4 v5 v6 v7
du_has'45'decidable'45'equality'45'left'45'factor_150 ::
  (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_has'45'decidable'45'equality'45'left'45'factor_150 v0 v1 v2 v3
  = let v4
          = coe
              v0
              (coe
                 MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                 (coe v2) (coe v1))
              (coe
                 MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                 (coe v3) (coe v1)) in
    case coe v4 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v5
        -> coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 erased
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v5
        -> coe
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
             (coe (\ v6 -> coe v5 erased))
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.decidable-equality.has-decidable-equality-right-factor
d_has'45'decidable'45'equality'45'right'45'factor_196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_has'45'decidable'45'equality'45'right'45'factor_196 ~v0 ~v1 ~v2
                                                      ~v3 v4 v5 v6 v7
  = du_has'45'decidable'45'equality'45'right'45'factor_196
      v4 v5 v6 v7
du_has'45'decidable'45'equality'45'right'45'factor_196 ::
  (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_has'45'decidable'45'equality'45'right'45'factor_196 v0 v1 v2 v3
  = let v4
          = coe
              v0
              (coe
                 MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                 (coe v1) (coe v2))
              (coe
                 MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                 (coe v1) (coe v3)) in
    case coe v4 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v5
        -> coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 erased
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v5
        -> coe
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
             (coe (\ v6 -> coe v5 erased))
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.decidable-equality.has-decidable-equality-retract-of
d_has'45'decidable'45'equality'45'retract'45'of_240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_has'45'decidable'45'equality'45'retract'45'of_240 ~v0 ~v1 ~v2 ~v3
                                                    v4 v5 v6 v7
  = du_has'45'decidable'45'equality'45'retract'45'of_240 v4 v5 v6 v7
du_has'45'decidable'45'equality'45'retract'45'of_240 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_has'45'decidable'45'equality'45'retract'45'of_240 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v4 v5
        -> coe
             seq (coe v5)
             (coe
                MAlonzo.Code.Qfoundation.QdecidableZ45Ztypes.du_is'45'decidable'45'retract'45'of_278
                (coe
                   MAlonzo.Code.QfoundationZ45Zcore.Qretractions.du_retract'45'eq_172
                   (coe v0))
                (coe v1 (coe v4 v2) (coe v4 v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.decidable-equality.has-decidable-equality-equiv
d_has'45'decidable'45'equality'45'equiv_264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_has'45'decidable'45'equality'45'equiv_264 ~v0 ~v1 ~v2 ~v3 v4 v5
                                            v6 v7
  = du_has'45'decidable'45'equality'45'equiv_264 v4 v5 v6 v7
du_has'45'decidable'45'equality'45'equiv_264 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_has'45'decidable'45'equality'45'equiv_264 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Qfoundation.QdecidableZ45Ztypes.du_is'45'decidable'45'equiv_312
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_equiv'45'ap_912)
      (coe
         v1
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
            v0 v2)
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
            v0 v3))
-- foundation.decidable-equality.has-decidable-equality-equiv'
d_has'45'decidable'45'equality'45'equiv''_284 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_has'45'decidable'45'equality'45'equiv''_284 ~v0 ~v1 ~v2 ~v3 v4
  = du_has'45'decidable'45'equality'45'equiv''_284 v4
du_has'45'decidable'45'equality'45'equiv''_284 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_has'45'decidable'45'equality'45'equiv''_284 v0
  = coe
      du_has'45'decidable'45'equality'45'equiv_264
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_inv'45'equiv_250
         (coe v0))
-- foundation.decidable-equality._.Eq-has-decidable-equality'
d_Eq'45'has'45'decidable'45'equality''_300 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> ()
d_Eq'45'has'45'decidable'45'equality''_300 = erased
-- foundation.decidable-equality._.Eq-has-decidable-equality
d_Eq'45'has'45'decidable'45'equality_316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  AgdaAny -> AgdaAny -> ()
d_Eq'45'has'45'decidable'45'equality_316 = erased
-- foundation.decidable-equality._.is-prop-Eq-has-decidable-equality'
d_is'45'prop'45'Eq'45'has'45'decidable'45'equality''_330 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'Eq'45'has'45'decidable'45'equality''_330 ~v0 ~v1
                                                         ~v2 ~v3 v4
  = du_is'45'prop'45'Eq'45'has'45'decidable'45'equality''_330 v4
du_is'45'prop'45'Eq'45'has'45'decidable'45'equality''_330 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'Eq'45'has'45'decidable'45'equality''_330 v0
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v1
        -> coe
             MAlonzo.Code.Qfoundation.QunitZ45Ztype.d_is'45'prop'45'unit_82
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v1
        -> \ v2 ->
             coe
               MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_is'45'prop'45'empty_88
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.decidable-equality._.is-prop-Eq-has-decidable-equality
d_is'45'prop'45'Eq'45'has'45'decidable'45'equality_350 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'Eq'45'has'45'decidable'45'equality_350 ~v0 ~v1 v2
                                                       v3 v4
  = du_is'45'prop'45'Eq'45'has'45'decidable'45'equality_350 v2 v3 v4
du_is'45'prop'45'Eq'45'has'45'decidable'45'equality_350 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'Eq'45'has'45'decidable'45'equality_350 v0 v1 v2
  = coe
      du_is'45'prop'45'Eq'45'has'45'decidable'45'equality''_330
      (coe v0 v1 v2)
-- foundation.decidable-equality._.refl-Eq-has-decidable-equality
d_refl'45'Eq'45'has'45'decidable'45'equality_362 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  AgdaAny -> AgdaAny
d_refl'45'Eq'45'has'45'decidable'45'equality_362 = erased
-- foundation.decidable-equality._.Eq-has-decidable-equality-eq
d_Eq'45'has'45'decidable'45'equality'45'eq_390 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny
d_Eq'45'has'45'decidable'45'equality'45'eq_390 = erased
-- foundation.decidable-equality._.eq-Eq-has-decidable-equality'
d_eq'45'Eq'45'has'45'decidable'45'equality''_402 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'Eq'45'has'45'decidable'45'equality''_402 = erased
-- foundation.decidable-equality._.eq-Eq-has-decidable-equality
d_eq'45'Eq'45'has'45'decidable'45'equality_426 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'Eq'45'has'45'decidable'45'equality_426 = erased
-- foundation.decidable-equality._.is-set-has-decidable-equality
d_is'45'set'45'has'45'decidable'45'equality_434 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'set'45'has'45'decidable'45'equality_434 ~v0 ~v1 ~v2
  = du_is'45'set'45'has'45'decidable'45'equality_434
du_is'45'set'45'has'45'decidable'45'equality_434 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'set'45'has'45'decidable'45'equality_434 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qsets.du_is'45'set'45'prop'45'in'45'id_146
-- foundation.decidable-equality.is-prop-has-decidable-equality
d_is'45'prop'45'has'45'decidable'45'equality_456 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'has'45'decidable'45'equality_456 v0 ~v1
  = du_is'45'prop'45'has'45'decidable'45'equality_456 v0
du_is'45'prop'45'has'45'decidable'45'equality_456 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'has'45'decidable'45'equality_456 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'prop'45'is'45'inhabited_38
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Qfoundation.Qpropositions.du_is'45'prop'45'Π_48 v0 v0
              (\ v2 ->
                 coe
                   MAlonzo.Code.Qfoundation.Qpropositions.du_is'45'prop'45'Π_48 v0 v0
                   (\ v3 ->
                      coe
                        MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.du_is'45'prop'45'coprod_264))))
-- foundation.decidable-equality.has-decidable-equality-Prop
d_has'45'decidable'45'equality'45'Prop_472 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_has'45'decidable'45'equality'45'Prop_472 v0 ~v1
  = du_has'45'decidable'45'equality'45'Prop_472 v0
du_has'45'decidable'45'equality'45'Prop_472 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_has'45'decidable'45'equality'45'Prop_472 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased
      (coe du_is'45'prop'45'has'45'decidable'45'equality_456 (coe v0))
-- foundation.decidable-equality.has-decidable-equality-Σ
d_has'45'decidable'45'equality'45'Σ_488 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_has'45'decidable'45'equality'45'Σ_488 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_has'45'decidable'45'equality'45'Σ_488 v4 v5 v6 v7
du_has'45'decidable'45'equality'45'Σ_488 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_has'45'decidable'45'equality'45'Σ_488 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v4 v5
        -> case coe v3 of
             MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v6 v7
               -> let v8 = coe v0 v4 v6 in
                  case coe v8 of
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v9
                      -> coe
                           MAlonzo.Code.Qfoundation.QdecidableZ45Ztypes.du_is'45'decidable'45'iff_250
                           erased
                           (\ v10 ->
                              coe
                                MAlonzo.Code.Qfoundation.QequalityZ45ZdependentZ45ZpairZ45Ztypes.du_pair'45'eq'45'Σ_44)
                           (coe
                              MAlonzo.Code.Qfoundation.QdecidableZ45Ztypes.du_is'45'decidable'45'equiv_312
                              (coe
                                 MAlonzo.Code.QfoundationZ45Zcore.QtypeZ45ZarithmeticZ45ZdependentZ45ZpairZ45Ztypes.du_left'45'unit'45'law'45'Σ'45'is'45'contr_52
                                 (coe v9))
                              (coe v1 v6 v5 v7))
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v9
                      -> coe
                           MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                           (coe (\ v10 -> coe v9 erased))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.decidable-equality.has-decidable-equality-fiber-has-decidable-equality-Σ
d_has'45'decidable'45'equality'45'fiber'45'has'45'decidable'45'equality'45'Σ_546 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_has'45'decidable'45'equality'45'fiber'45'has'45'decidable'45'equality'45'Σ_546 ~v0
                                                                                 ~v1 ~v2 ~v3 ~v4 v5
                                                                                 v6
  = du_has'45'decidable'45'equality'45'fiber'45'has'45'decidable'45'equality'45'Σ_546
      v5 v6
du_has'45'decidable'45'equality'45'fiber'45'has'45'decidable'45'equality'45'Σ_546 ::
  (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_has'45'decidable'45'equality'45'fiber'45'has'45'decidable'45'equality'45'Σ_546 v0
                                                                                  v1
  = coe
      du_has'45'decidable'45'equality'45'equiv''_284
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QfibersZ45ZofZ45Zmaps.du_equiv'45'fib'45'pr1_194
         (coe v1))
      (coe
         du_has'45'decidable'45'equality'45'Σ_488 (coe v0)
         (coe
            (\ v2 v3 v4 ->
               coe du_has'45'decidable'45'equality'45'is'45'prop_20)))
-- foundation.decidable-equality.has-decidable-equality-base-has-decidable-equality-Σ
d_has'45'decidable'45'equality'45'base'45'has'45'decidable'45'equality'45'Σ_572 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_has'45'decidable'45'equality'45'base'45'has'45'decidable'45'equality'45'Σ_572 ~v0
                                                                                ~v1 ~v2 ~v3 v4 v5
                                                                                ~v6
  = du_has'45'decidable'45'equality'45'base'45'has'45'decidable'45'equality'45'Σ_572
      v4 v5
du_has'45'decidable'45'equality'45'base'45'has'45'decidable'45'equality'45'Σ_572 ::
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_has'45'decidable'45'equality'45'base'45'has'45'decidable'45'equality'45'Σ_572 v0
                                                                                 v1
  = coe
      du_has'45'decidable'45'equality'45'equiv''_284
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QfibersZ45ZofZ45Zmaps.du_equiv'45'total'45'fib_238
         (coe
            MAlonzo.Code.Qfoundation.Qsections.du_map'45'section_18 (coe v0)))
      (coe
         du_has'45'decidable'45'equality'45'Σ_488 (coe v1)
         (coe
            (\ v2 v3 v4 ->
               coe du_has'45'decidable'45'equality'45'is'45'prop_20)))
-- foundation.decidable-equality._.has-decidable-equality-coprod
d_has'45'decidable'45'equality'45'coprod_594 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_has'45'decidable'45'equality'45'coprod_594 ~v0 ~v1 ~v2 ~v3 v4 v5
                                             v6 v7
  = du_has'45'decidable'45'equality'45'coprod_594 v4 v5 v6 v7
du_has'45'decidable'45'equality'45'coprod_594 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_has'45'decidable'45'equality'45'coprod_594 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v4
        -> case coe v3 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v5
               -> coe
                    MAlonzo.Code.Qfoundation.QdecidableZ45Ztypes.du_is'45'decidable'45'iff_250
                    erased erased (coe v0 v4 v5)
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v5
               -> coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v4
        -> case coe v3 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v5
               -> coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 erased
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v5
               -> coe
                    MAlonzo.Code.Qfoundation.QdecidableZ45Ztypes.du_is'45'decidable'45'iff_250
                    erased erased (coe v1 v4 v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.decidable-equality._.has-decidable-equality-left-summand
d_has'45'decidable'45'equality'45'left'45'summand_628 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_has'45'decidable'45'equality'45'left'45'summand_628 ~v0 ~v1 ~v2
                                                      ~v3 v4 v5 v6
  = du_has'45'decidable'45'equality'45'left'45'summand_628 v4 v5 v6
du_has'45'decidable'45'equality'45'left'45'summand_628 ::
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_has'45'decidable'45'equality'45'left'45'summand_628 v0 v1 v2
  = coe
      MAlonzo.Code.Qfoundation.QdecidableZ45Ztypes.du_is'45'decidable'45'iff_250
      erased erased
      (coe
         v0
         (coe
            MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 (coe v1))
         (coe
            MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 (coe v2)))
-- foundation.decidable-equality._.has-decidable-equality-right-summand
d_has'45'decidable'45'equality'45'right'45'summand_636 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_has'45'decidable'45'equality'45'right'45'summand_636 ~v0 ~v1 ~v2
                                                       ~v3 v4 v5 v6
  = du_has'45'decidable'45'equality'45'right'45'summand_636 v4 v5 v6
du_has'45'decidable'45'equality'45'right'45'summand_636 ::
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_has'45'decidable'45'equality'45'right'45'summand_636 v0 v1 v2
  = coe
      MAlonzo.Code.Qfoundation.QdecidableZ45Ztypes.du_is'45'decidable'45'iff_250
      erased erased
      (coe
         v0
         (coe
            MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 (coe v1))
         (coe
            MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 (coe v2)))
