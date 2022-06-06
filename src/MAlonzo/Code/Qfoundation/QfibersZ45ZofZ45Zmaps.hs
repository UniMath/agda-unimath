{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QfibersZ45ZofZ45Zmaps where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtypeZ45ZarithmeticZ45ZcartesianZ45ZproductZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtypeZ45ZarithmeticZ45ZdependentZ45ZpairZ45Ztypes

-- foundation.fibers-of-maps.map-reduce-Π-fib
d_map'45'reduce'45'Π'45'fib_28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   ()) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   AgdaAny) ->
  AgdaAny -> AgdaAny
d_map'45'reduce'45'Π'45'fib_28 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 v8
  = du_map'45'reduce'45'Π'45'fib_28 v5 v7 v8
du_map'45'reduce'45'Π'45'fib_28 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   AgdaAny) ->
  AgdaAny -> AgdaAny
du_map'45'reduce'45'Π'45'fib_28 v0 v1 v2
  = coe
      v1 (coe v0 v2)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe v2) erased)
-- foundation.fibers-of-maps.inv-map-reduce-Π-fib
d_inv'45'map'45'reduce'45'Π'45'fib_62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   ()) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
d_inv'45'map'45'reduce'45'Π'45'fib_62 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                      v7 ~v8 v9
  = du_inv'45'map'45'reduce'45'Π'45'fib_62 v7 v9
du_inv'45'map'45'reduce'45'Π'45'fib_62 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
du_inv'45'map'45'reduce'45'Π'45'fib_62 v0 v1
  = case coe v1 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
        -> coe v0 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.fibers-of-maps.issec-inv-map-reduce-Π-fib
d_issec'45'inv'45'map'45'reduce'45'Π'45'fib_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'inv'45'map'45'reduce'45'Π'45'fib_90 = erased
-- foundation.fibers-of-maps.isretr-inv-map-reduce-Π-fib'
d_isretr'45'inv'45'map'45'reduce'45'Π'45'fib''_124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   ()) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'inv'45'map'45'reduce'45'Π'45'fib''_124 = erased
-- foundation.fibers-of-maps.isretr-inv-map-reduce-Π-fib
d_isretr'45'inv'45'map'45'reduce'45'Π'45'fib_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   ()) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'inv'45'map'45'reduce'45'Π'45'fib_152 = erased
-- foundation.fibers-of-maps.is-equiv-map-reduce-Π-fib
d_is'45'equiv'45'map'45'reduce'45'Π'45'fib_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'reduce'45'Π'45'fib_180 ~v0 ~v1 ~v2 ~v3 ~v4
                                               ~v5 ~v6
  = du_is'45'equiv'45'map'45'reduce'45'Π'45'fib_180
du_is'45'equiv'45'map'45'reduce'45'Π'45'fib_180 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'reduce'45'Π'45'fib_180
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (\ v0 v1 v2 -> coe du_inv'45'map'45'reduce'45'Π'45'fib_62 v0 v2)
      erased erased
-- foundation.fibers-of-maps.reduce-Π-fib'
d_reduce'45'Π'45'fib''_210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_reduce'45'Π'45'fib''_210 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_reduce'45'Π'45'fib''_210 v5
du_reduce'45'Π'45'fib''_210 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_reduce'45'Π'45'fib''_210 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_map'45'reduce'45'Π'45'fib_28 (coe v0))
      (coe du_is'45'equiv'45'map'45'reduce'45'Π'45'fib_180)
-- foundation.fibers-of-maps.reduce-Π-fib
d_reduce'45'Π'45'fib_238 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_reduce'45'Π'45'fib_238 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_reduce'45'Π'45'fib_238 v5
du_reduce'45'Π'45'fib_238 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_reduce'45'Π'45'fib_238 v0
  = coe du_reduce'45'Π'45'fib''_210 (coe v0)
-- foundation.fibers-of-maps.fib-comp
d_fib'45'comp_268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_fib'45'comp_268 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8
  = du_fib'45'comp_268 v7
du_fib'45'comp_268 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_fib'45'comp_268 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QtypeZ45ZarithmeticZ45ZdependentZ45ZpairZ45Ztypes.du_equiv'45'left'45'swap'45'Σ_464)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes.du_equiv'45'tot_340
         (coe
            (\ v1 ->
               coe
                 MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386
                 (coe
                    MAlonzo.Code.QfoundationZ45Zcore.QtypeZ45ZarithmeticZ45ZdependentZ45ZpairZ45Ztypes.du_inv'45'assoc'45'Σ_166)
                 (coe
                    MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386
                    (coe
                       MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes.du_equiv'45'tot_340
                       (coe
                          (\ v2 ->
                             coe
                               MAlonzo.Code.QfoundationZ45Zcore.QtypeZ45ZarithmeticZ45ZcartesianZ45ZproductZ45Ztypes.du_commutative'45'prod_50)))
                    (coe
                       MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386
                       (coe
                          MAlonzo.Code.QfoundationZ45Zcore.QtypeZ45ZarithmeticZ45ZdependentZ45ZpairZ45Ztypes.du_assoc'45'Σ_160)
                       (coe
                          MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_inv'45'equiv_250
                          (coe
                             MAlonzo.Code.QfoundationZ45Zcore.QtypeZ45ZarithmeticZ45ZdependentZ45ZpairZ45Ztypes.du_left'45'unit'45'law'45'Σ'45'is'45'contr_52
                             (coe
                                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                                (coe v0 v1) erased))))))))
