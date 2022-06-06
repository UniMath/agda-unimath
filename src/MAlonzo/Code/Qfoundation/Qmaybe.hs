{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.Qmaybe where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QdecidableZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QequalityZ45ZcoproductZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QtypeZ45ZarithmeticZ45ZemptyZ45Ztype

-- foundation.maybe.Maybe
d_Maybe_6 :: MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> ()
d_Maybe_6 = erased
-- foundation.maybe.unit-Maybe
d_unit'45'Maybe_14 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_unit'45'Maybe_14 ~v0 ~v1 = du_unit'45'Maybe_14
du_unit'45'Maybe_14 ::
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_unit'45'Maybe_14
  = coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22
-- foundation.maybe.exception-Maybe
d_exception'45'Maybe_20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_exception'45'Maybe_20 ~v0 ~v1 = du_exception'45'Maybe_20
du_exception'45'Maybe_20 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_exception'45'Maybe_20
  = coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 erased
-- foundation.maybe.is-exception-Maybe
d_is'45'exception'45'Maybe_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> ()
d_is'45'exception'45'Maybe_30 = erased
-- foundation.maybe.is-not-exception-Maybe
d_is'45'not'45'exception'45'Maybe_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> ()
d_is'45'not'45'exception'45'Maybe_42 = erased
-- foundation.maybe.is-value-Maybe
d_is'45'value'45'Maybe_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> ()
d_is'45'value'45'Maybe_50 = erased
-- foundation.maybe.value-is-value-Maybe
d_value'45'is'45'value'45'Maybe_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
d_value'45'is'45'value'45'Maybe_66 ~v0 ~v1 ~v2
  = du_value'45'is'45'value'45'Maybe_66
du_value'45'is'45'value'45'Maybe_66 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
du_value'45'is'45'value'45'Maybe_66
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
-- foundation.maybe.eq-is-value-Maybe
d_eq'45'is'45'value'45'Maybe_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'is'45'value'45'Maybe_78 = erased
-- foundation.maybe.maybe-structure
d_maybe'45'structure_88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> ()
d_maybe'45'structure_88 = erased
-- foundation.maybe.is-emb-unit-Maybe
d_is'45'emb'45'unit'45'Maybe_100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'emb'45'unit'45'Maybe_100 ~v0 ~v1
  = du_is'45'emb'45'unit'45'Maybe_100
du_is'45'emb'45'unit'45'Maybe_100 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'emb'45'unit'45'Maybe_100
  = coe
      MAlonzo.Code.Qfoundation.QequalityZ45ZcoproductZ45Ztypes.du_is'45'emb'45'inl_222
-- foundation.maybe.emb-unit-Maybe
d_emb'45'unit'45'Maybe_110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_emb'45'unit'45'Maybe_110 ~v0 ~v1 = du_emb'45'unit'45'Maybe_110
du_emb'45'unit'45'Maybe_110 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_emb'45'unit'45'Maybe_110
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_unit'45'Maybe_14) (coe du_is'45'emb'45'unit'45'Maybe_100)
-- foundation.maybe.is-injective-unit-Maybe
d_is'45'injective'45'unit'45'Maybe_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'injective'45'unit'45'Maybe_120 = erased
-- foundation.maybe.is-decidable-is-exception-Maybe
d_is'45'decidable'45'is'45'exception'45'Maybe_128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'is'45'exception'45'Maybe_128 ~v0 ~v1 v2
  = du_is'45'decidable'45'is'45'exception'45'Maybe_128 v2
du_is'45'decidable'45'is'45'exception'45'Maybe_128 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_is'45'decidable'45'is'45'exception'45'Maybe_128 v0
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v1
        -> coe
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
             (coe
                (\ v2 ->
                   coe
                     MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_ex'45'falso_18
                     erased))
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v1
        -> coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.maybe.is-decidable-is-not-exception-Maybe
d_is'45'decidable'45'is'45'not'45'exception'45'Maybe_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'is'45'not'45'exception'45'Maybe_144 ~v0 ~v1 v2
  = du_is'45'decidable'45'is'45'not'45'exception'45'Maybe_144 v2
du_is'45'decidable'45'is'45'not'45'exception'45'Maybe_144 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_is'45'decidable'45'is'45'not'45'exception'45'Maybe_144 v0
  = coe
      MAlonzo.Code.Qfoundation.QdecidableZ45Ztypes.du_is'45'decidable'45'neg_234
      (coe du_is'45'decidable'45'is'45'exception'45'Maybe_128 (coe v0))
-- foundation.maybe.is-not-exception-unit-Maybe
d_is'45'not'45'exception'45'unit'45'Maybe_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_is'45'not'45'exception'45'unit'45'Maybe_154 = erased
-- foundation.maybe.decide-Maybe
d_decide'45'Maybe_168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_decide'45'Maybe_168 ~v0 ~v1 v2 = du_decide'45'Maybe_168 v2
du_decide'45'Maybe_168 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_decide'45'Maybe_168 v0
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v1
        -> coe
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22
             (coe
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                (coe v1) erased)
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v1
        -> coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.maybe.is-not-exception-is-value-Maybe
d_is'45'not'45'exception'45'is'45'value'45'Maybe_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_is'45'not'45'exception'45'is'45'value'45'Maybe_178 = erased
-- foundation.maybe.is-value-is-not-exception-Maybe
d_is'45'value'45'is'45'not'45'exception'45'Maybe_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'value'45'is'45'not'45'exception'45'Maybe_192 ~v0 ~v1 v2 ~v3
  = du_is'45'value'45'is'45'not'45'exception'45'Maybe_192 v2
du_is'45'value'45'is'45'not'45'exception'45'Maybe_192 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'value'45'is'45'not'45'exception'45'Maybe_192 v0
  = coe
      MAlonzo.Code.Qfoundation.QtypeZ45ZarithmeticZ45ZemptyZ45Ztype.du_map'45'right'45'unit'45'law'45'coprod'45'is'45'empty_238
      (coe du_decide'45'Maybe_168 (coe v0))
-- foundation.maybe.value-is-not-exception-Maybe
d_value'45'is'45'not'45'exception'45'Maybe_204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  AgdaAny
d_value'45'is'45'not'45'exception'45'Maybe_204 ~v0 ~v1 v2 ~v3
  = du_value'45'is'45'not'45'exception'45'Maybe_204 v2
du_value'45'is'45'not'45'exception'45'Maybe_204 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> AgdaAny
du_value'45'is'45'not'45'exception'45'Maybe_204 v0
  = coe
      du_value'45'is'45'value'45'Maybe_66
      (coe
         du_is'45'value'45'is'45'not'45'exception'45'Maybe_192 (coe v0))
-- foundation.maybe.eq-is-not-exception-Maybe
d_eq'45'is'45'not'45'exception'45'Maybe_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'is'45'not'45'exception'45'Maybe_218 = erased
