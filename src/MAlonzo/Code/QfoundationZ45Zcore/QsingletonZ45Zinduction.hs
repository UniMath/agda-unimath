{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QfoundationZ45Zcore.QsingletonZ45Zinduction where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qfunctions
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes

-- foundation-core.singleton-induction.is-singleton
d_is'45'singleton_10 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> AgdaAny -> ()
d_is'45'singleton_10 = erased
-- foundation-core.singleton-induction.ind-is-singleton
d_ind'45'is'45'singleton_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   (AgdaAny -> ()) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny -> ()) -> AgdaAny -> AgdaAny -> AgdaAny
d_ind'45'is'45'singleton_34 ~v0 v1 ~v2 ~v3 v4 v5
  = du_ind'45'is'45'singleton_34 v1 v4 v5
du_ind'45'is'45'singleton_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   (AgdaAny -> ()) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny -> ()) -> AgdaAny -> AgdaAny -> AgdaAny
du_ind'45'is'45'singleton_34 v0 v1 v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
      (coe v1 v0 v2)
-- foundation-core.singleton-induction.comp-is-singleton
d_comp'45'is'45'singleton_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   (AgdaAny -> ()) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_comp'45'is'45'singleton_56 = erased
-- foundation-core.singleton-induction.ind-singleton-is-contr
d_ind'45'singleton'45'is'45'contr_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> ()) -> AgdaAny -> AgdaAny -> AgdaAny
d_ind'45'singleton'45'is'45'contr_78 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7
  = du_ind'45'singleton'45'is'45'contr_78 v6
du_ind'45'singleton'45'is'45'contr_78 :: AgdaAny -> AgdaAny
du_ind'45'singleton'45'is'45'contr_78 v0 = coe v0
-- foundation-core.singleton-induction.comp-singleton-is-contr
d_comp'45'singleton'45'is'45'contr_102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_comp'45'singleton'45'is'45'contr_102 = erased
-- foundation-core.singleton-induction.is-singleton-is-contr
d_is'45'singleton'45'is'45'contr_122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'singleton'45'is'45'contr_122 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_is'45'singleton'45'is'45'contr_122
du_is'45'singleton'45'is'45'contr_122 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'singleton'45'is'45'contr_122
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe (\ v0 v1 -> v0)) erased
-- foundation-core.singleton-induction.is-contr-ind-singleton
d_is'45'contr'45'ind'45'singleton_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   (AgdaAny -> ()) -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'ind'45'singleton_148 v0 ~v1 v2 v3
  = du_is'45'contr'45'ind'45'singleton_148 v0 v2 v3
du_is'45'contr'45'ind'45'singleton_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   (AgdaAny -> ()) -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'ind'45'singleton_148 v0 v1 v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe v1) (coe v2 v0 erased erased)
-- foundation-core.singleton-induction.is-contr-is-singleton
d_is'45'contr'45'is'45'singleton_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   (AgdaAny -> ()) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'is'45'singleton_172 v0 ~v1 v2 v3
  = du_is'45'contr'45'is'45'singleton_172 v0 v2 v3
du_is'45'contr'45'is'45'singleton_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   (AgdaAny -> ()) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'is'45'singleton_172 v0 v1 v2
  = coe
      du_is'45'contr'45'ind'45'singleton_148 (coe v0) (coe v1)
      (coe
         (\ v3 v4 ->
            MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
              (coe v2 v3 v4)))
-- foundation-core.singleton-induction.is-singleton-total-path
d_is'45'singleton'45'total'45'path_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'singleton'45'total'45'path_192 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_is'45'singleton'45'total'45'path_192
du_is'45'singleton'45'total'45'path_192 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'singleton'45'total'45'path_192
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du__'8728'__36
         (coe
            (\ v0 ->
               coe
                 MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.du_ind'45'Σ_50))
         (coe (\ v0 v1 v2 -> v0)))
      erased
