{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QfoundationZ45Zcore.QequalityZ45ZfibersZ45ZofZ45Zmaps where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QequalityZ45ZdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qfunctions
import qualified MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QidentityZ45Ztypes

-- foundation-core.equality-fibers-of-maps._.fib-ap-eq-fib-fiberwise
d_fib'45'ap'45'eq'45'fib'45'fiberwise_28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_fib'45'ap'45'eq'45'fib'45'fiberwise_28 = erased
-- foundation-core.equality-fibers-of-maps._.is-fiberwise-equiv-fib-ap-eq-fib-fiberwise
d_is'45'fiberwise'45'equiv'45'fib'45'ap'45'eq'45'fib'45'fiberwise_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'fiberwise'45'equiv'45'fib'45'ap'45'eq'45'fib'45'fiberwise_38 ~v0
                                                                     ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 ~v8
  = du_is'45'fiberwise'45'equiv'45'fib'45'ap'45'eq'45'fib'45'fiberwise_38
      v6 v7
du_is'45'fiberwise'45'equiv'45'fib'45'ap'45'eq'45'fib'45'fiberwise_38 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'fiberwise'45'equiv'45'fib'45'ap'45'eq'45'fib'45'fiberwise_38 v0
                                                                      v1
  = coe
      seq (coe v0)
      (coe
         seq (coe v1)
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'comp_332
            (coe
               MAlonzo.Code.Qfoundation.QidentityZ45Ztypes.du_is'45'equiv'45'concat_84)
            (coe
               MAlonzo.Code.Qfoundation.QidentityZ45Ztypes.du_is'45'equiv'45'inv_18)))
-- foundation-core.equality-fibers-of-maps._.fib-ap-eq-fib
d_fib'45'ap'45'eq'45'fib_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_fib'45'ap'45'eq'45'fib_48 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_fib'45'ap'45'eq'45'fib_48
du_fib'45'ap'45'eq'45'fib_48 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_fib'45'ap'45'eq'45'fib_48
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased erased
-- foundation-core.equality-fibers-of-maps._.triangle-fib-ap-eq-fib
d_triangle'45'fib'45'ap'45'eq'45'fib_58 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_triangle'45'fib'45'ap'45'eq'45'fib_58 = erased
-- foundation-core.equality-fibers-of-maps._.is-equiv-fib-ap-eq-fib
d_is'45'equiv'45'fib'45'ap'45'eq'45'fib_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'fib'45'ap'45'eq'45'fib_66 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
                                           v6 v7
  = du_is'45'equiv'45'fib'45'ap'45'eq'45'fib_66 v6 v7
du_is'45'equiv'45'fib'45'ap'45'eq'45'fib_66 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'fib'45'ap'45'eq'45'fib_66 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'comp_332
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QequalityZ45ZdependentZ45ZpairZ45Ztypes.du_is'45'equiv'45'pair'45'eq'45'Σ_114)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes.du_is'45'equiv'45'tot'45'is'45'fiberwise'45'equiv_308
         (\ v2 ->
            coe
              du_is'45'fiberwise'45'equiv'45'fib'45'ap'45'eq'45'fib'45'fiberwise_38
              (coe v0) (coe v1)))
-- foundation-core.equality-fibers-of-maps._.equiv-fib-ap-eq-fib
d_equiv'45'fib'45'ap'45'eq'45'fib_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'fib'45'ap'45'eq'45'fib_76 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du_equiv'45'fib'45'ap'45'eq'45'fib_76 v6 v7
du_equiv'45'fib'45'ap'45'eq'45'fib_76 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'fib'45'ap'45'eq'45'fib_76 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (\ v2 -> coe du_fib'45'ap'45'eq'45'fib_48)
      (coe du_is'45'equiv'45'fib'45'ap'45'eq'45'fib_66 (coe v0) (coe v1))
-- foundation-core.equality-fibers-of-maps._.eq-fib-fib-ap
d_eq'45'fib'45'fib'45'ap_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_eq'45'fib'45'fib'45'ap_106 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_eq'45'fib'45'fib'45'ap_106
du_eq'45'fib'45'fib'45'ap_106 ::
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_eq'45'fib'45'fib'45'ap_106
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du__'8728'__36
      (coe (\ v0 v1 -> v1)) (\ v0 -> coe du_fib'45'ap'45'eq'45'fib_48)
-- foundation-core.equality-fibers-of-maps._.is-equiv-eq-fib-fib-ap
d_is'45'equiv'45'eq'45'fib'45'fib'45'ap_112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'eq'45'fib'45'fib'45'ap_112 ~v0 ~v1 ~v2 ~v3 ~v4 v5
                                            v6 v7
  = du_is'45'equiv'45'eq'45'fib'45'fib'45'ap_112 v5 v6 v7
du_is'45'equiv'45'eq'45'fib'45'fib'45'ap_112 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'eq'45'fib'45'fib'45'ap_112 v0 v1 v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'comp_332
      (coe
         du_is'45'equiv'45'fib'45'ap'45'eq'45'fib_66
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
            (coe v0) (coe v2))
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
            (coe v1) erased))
      (coe
         MAlonzo.Code.Qfoundation.QidentityZ45Ztypes.du_is'45'equiv'45'tr_270)
