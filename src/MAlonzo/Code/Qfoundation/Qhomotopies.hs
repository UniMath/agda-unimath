{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.Qhomotopies where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Zsystems
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QfunctionZ45Zextensionality
import qualified MAlonzo.Code.Qfoundation.QfunctorialityZ45ZdependentZ45ZfunctionZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QidentityZ45Ztypes

-- foundation.homotopies._.inv-con-htpy
d_inv'45'con'45'htpy_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_inv'45'con'45'htpy_30 = erased
-- foundation.homotopies._.con-inv-htpy
d_con'45'inv'45'htpy_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_con'45'inv'45'htpy_48 = erased
-- foundation.homotopies._.ap-concat-htpy
d_ap'45'concat'45'htpy_86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_ap'45'concat'45'htpy_86 = erased
-- foundation.homotopies._.ap-concat-htpy'
d_ap'45'concat'45'htpy''_104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_ap'45'concat'45'htpy''_104 = erased
-- foundation.homotopies._.ap-inv-htpy
d_ap'45'inv'45'htpy_138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_ap'45'inv'45'htpy_138 = erased
-- foundation.homotopies._.left-whisk-inv-htpy
d_left'45'whisk'45'inv'45'htpy_168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'whisk'45'inv'45'htpy_168 = erased
-- foundation.homotopies._.right-whisk-inv-htpy
d_right'45'whisk'45'inv'45'htpy_184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'whisk'45'inv'45'htpy_184 = erased
-- foundation.homotopies._.is-contr-total-htpy
d_is'45'contr'45'total'45'htpy_210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'total'45'htpy_210 v0 v1 ~v2 ~v3 v4
  = du_is'45'contr'45'total'45'htpy_210 v0 v1 v4
du_is'45'contr'45'total'45'htpy_210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'total'45'htpy_210 v0 v1 v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'contr'45'equiv''_216
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes.du_equiv'45'tot_340
         (coe
            (\ v3 ->
               coe
                 MAlonzo.Code.Qfoundation.QfunctionZ45Zextensionality.du_equiv'45'funext_60
                 (coe v0) (coe v1) (coe v2) (coe v3))))
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'contr'45'total'45'path_96
         (coe v2))
-- foundation.homotopies._.is-contr-total-htpy'
d_is'45'contr'45'total'45'htpy''_220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'total'45'htpy''_220 v0 v1 ~v2 ~v3 v4
  = du_is'45'contr'45'total'45'htpy''_220 v0 v1 v4
du_is'45'contr'45'total'45'htpy''_220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'total'45'htpy''_220 v0 v1 v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'contr'45'equiv''_216
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes.du_equiv'45'tot_340
         (coe
            (\ v3 ->
               coe
                 MAlonzo.Code.Qfoundation.QfunctionZ45Zextensionality.du_equiv'45'funext_60
                 (coe v0) (coe v1) (coe v3) (coe v2))))
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'contr'45'total'45'path''_108
         (coe v2))
-- foundation.homotopies.ev-refl-htpy
d_ev'45'refl'45'htpy_254 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  ((AgdaAny -> AgdaAny) ->
   (AgdaAny ->
    MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
   ()) ->
  ((AgdaAny -> AgdaAny) ->
   (AgdaAny ->
    MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
   AgdaAny) ->
  AgdaAny
d_ev'45'refl'45'htpy_254 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7
  = du_ev'45'refl'45'htpy_254 v5 v7
du_ev'45'refl'45'htpy_254 ::
  (AgdaAny -> AgdaAny) ->
  ((AgdaAny -> AgdaAny) ->
   (AgdaAny ->
    MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
   AgdaAny) ->
  AgdaAny
du_ev'45'refl'45'htpy_254 v0 v1 = coe v1 v0 erased
-- foundation.homotopies.IND-HTPY
d_IND'45'HTPY_276 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> (AgdaAny -> ()) -> (AgdaAny -> AgdaAny) -> ()
d_IND'45'HTPY_276 = erased
-- foundation.homotopies.IND-HTPY-FUNEXT
d_IND'45'HTPY'45'FUNEXT_310 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  ((AgdaAny -> AgdaAny) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  ((AgdaAny -> AgdaAny) ->
   (AgdaAny ->
    MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
   ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_IND'45'HTPY'45'FUNEXT_310 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_IND'45'HTPY'45'FUNEXT_310
du_IND'45'HTPY'45'FUNEXT_310 ::
  ((AgdaAny -> AgdaAny) ->
   (AgdaAny ->
    MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
   ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_IND'45'HTPY'45'FUNEXT_310 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Zsystems.du_Ind'45'identity'45'system_56
-- foundation.homotopies.FUNEXT-IND-HTPY
d_FUNEXT'45'IND'45'HTPY_336 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   ((AgdaAny -> AgdaAny) ->
    (AgdaAny ->
     MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
    ()) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_FUNEXT'45'IND'45'HTPY_336 ~v0 ~v1 ~v2 ~v3 v4 ~v5
  = du_FUNEXT'45'IND'45'HTPY_336 v4
du_FUNEXT'45'IND'45'HTPY_336 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_FUNEXT'45'IND'45'HTPY_336 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Zsystems.du_fundamental'45'theorem'45'id'45'IND'45'identity'45'system_102
      (coe v0)
-- foundation.homotopies.Ind-htpy
d_Ind'45'htpy_358 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  ((AgdaAny -> AgdaAny) ->
   (AgdaAny ->
    MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
   ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_Ind'45'htpy_358 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_Ind'45'htpy_358
du_Ind'45'htpy_358 ::
  ((AgdaAny -> AgdaAny) ->
   (AgdaAny ->
    MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
   ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_Ind'45'htpy_358 = coe du_IND'45'HTPY'45'FUNEXT_310
-- foundation.homotopies.ind-htpy
d_ind'45'htpy_388 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  ((AgdaAny -> AgdaAny) ->
   (AgdaAny ->
    MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
   ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  AgdaAny
d_ind'45'htpy_388 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8
  = du_ind'45'htpy_388 v7 v8
du_ind'45'htpy_388 ::
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  AgdaAny
du_ind'45'htpy_388 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
      (coe du_Ind'45'htpy_358 erased) v0 v1
-- foundation.homotopies.comp-htpy
d_comp'45'htpy_420 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  ((AgdaAny -> AgdaAny) ->
   (AgdaAny ->
    MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
   ()) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_comp'45'htpy_420 = erased
-- foundation.homotopies.is-equiv-inv-htpy
d_is'45'equiv'45'inv'45'htpy_440 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'inv'45'htpy_440 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_is'45'equiv'45'inv'45'htpy_440
du_is'45'equiv'45'inv'45'htpy_440 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'inv'45'htpy_440
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      erased erased erased
-- foundation.homotopies.equiv-inv-htpy
d_equiv'45'inv'45'htpy_468 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'inv'45'htpy_468 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_equiv'45'inv'45'htpy_468
du_equiv'45'inv'45'htpy_468 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'inv'45'htpy_468
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe du_is'45'equiv'45'inv'45'htpy_440)
-- foundation.homotopies.is-equiv-concat-htpy
d_is'45'equiv'45'concat'45'htpy_498 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'concat'45'htpy_498 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_is'45'equiv'45'concat'45'htpy_498 v5
du_is'45'equiv'45'concat'45'htpy_498 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'concat'45'htpy_498 v0
  = coe
      du_ind'45'htpy_388
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'id_90))
      (coe v0)
-- foundation.homotopies.equiv-concat-htpy
d_equiv'45'concat'45'htpy_536 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'concat'45'htpy_536 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7
  = du_equiv'45'concat'45'htpy_536 v5 v7
du_equiv'45'concat'45'htpy_536 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'concat'45'htpy_536 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe du_is'45'equiv'45'concat'45'htpy_498 v0 erased v1)
-- foundation.homotopies.inv-concat-htpy'
d_inv'45'concat'45'htpy''_564 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_inv'45'concat'45'htpy''_564 = erased
-- foundation.homotopies.issec-inv-concat-htpy'
d_issec'45'inv'45'concat'45'htpy''_590 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'inv'45'concat'45'htpy''_590 = erased
-- foundation.homotopies.isretr-inv-concat-htpy'
d_isretr'45'inv'45'concat'45'htpy''_620 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'inv'45'concat'45'htpy''_620 = erased
-- foundation.homotopies.is-equiv-concat-htpy'
d_is'45'equiv'45'concat'45'htpy''_650 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'concat'45'htpy''_650 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                      ~v7
  = du_is'45'equiv'45'concat'45'htpy''_650
du_is'45'equiv'45'concat'45'htpy''_650 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'concat'45'htpy''_650
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      erased erased erased
-- foundation.homotopies.equiv-concat-htpy'
d_equiv'45'concat'45'htpy''_676 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'concat'45'htpy''_676 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_equiv'45'concat'45'htpy''_676
du_equiv'45'concat'45'htpy''_676 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'concat'45'htpy''_676
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe du_is'45'equiv'45'concat'45'htpy''_650)
-- foundation.homotopies.is-equiv-inv-con-htpy
d_is'45'equiv'45'inv'45'con'45'htpy_708 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'inv'45'con'45'htpy_708 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                        ~v7 ~v8 ~v9
  = du_is'45'equiv'45'inv'45'con'45'htpy_708 v0
du_is'45'equiv'45'inv'45'con'45'htpy_708 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'inv'45'con'45'htpy_708 v0
  = coe
      MAlonzo.Code.Qfoundation.QfunctorialityZ45ZdependentZ45ZfunctionZ45Ztypes.du_is'45'equiv'45'map'45'Π_152
      (coe v0)
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Qfoundation.QidentityZ45Ztypes.du_is'45'equiv'45'inv'45'con_300))
-- foundation.homotopies.equiv-inv-con-htpy
d_equiv'45'inv'45'con'45'htpy_740 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'inv'45'con'45'htpy_740 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                  ~v8 ~v9
  = du_equiv'45'inv'45'con'45'htpy_740 v0
du_equiv'45'inv'45'con'45'htpy_740 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'inv'45'con'45'htpy_740 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe du_is'45'equiv'45'inv'45'con'45'htpy_708 (coe v0))
-- foundation.homotopies.is-equiv-con-inv-htpy
d_is'45'equiv'45'con'45'inv'45'htpy_776 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'con'45'inv'45'htpy_776 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                        ~v7 ~v8 ~v9
  = du_is'45'equiv'45'con'45'inv'45'htpy_776 v0
du_is'45'equiv'45'con'45'inv'45'htpy_776 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'con'45'inv'45'htpy_776 v0
  = coe
      MAlonzo.Code.Qfoundation.QfunctorialityZ45ZdependentZ45ZfunctionZ45Ztypes.du_is'45'equiv'45'map'45'Π_152
      (coe v0)
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Qfoundation.QidentityZ45Ztypes.du_is'45'equiv'45'con'45'inv_332))
-- foundation.homotopies.equiv-con-inv-htpy
d_equiv'45'con'45'inv'45'htpy_808 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'con'45'inv'45'htpy_808 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                  ~v8 ~v9
  = du_equiv'45'con'45'inv'45'htpy_808 v0
du_equiv'45'con'45'inv'45'htpy_808 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'con'45'inv'45'htpy_808 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe du_is'45'equiv'45'con'45'inv'45'htpy_776 (coe v0))
