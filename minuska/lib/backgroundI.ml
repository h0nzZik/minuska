open Libminuskapluginbase
open Pluginbase

type ('vr, 'v, 'nv, 'hv, 'prg, 'ts, 'fs, 'ps, 'qs, 'ats, 'ms, 'hps) backgroundI =
  {
    v_edc             : 'v Extracted.eDC ;
    hv_edc            : 'hv Extracted.eDC ;
    nv_edc            : 'nv Extracted.eDC ;
    vr_edc            : 'vr Extracted.eDC ;
    vr_inf            : 'vr Extracted.infinite ;
    ts_edc            : 'ts Extracted.eDC ;
    fs_edc            : 'fs Extracted.eDC ;
    ps_edc            : 'ps Extracted.eDC ;
    ats_edc           : 'ats Extracted.eDC ;
    ms_edc            : 'ms Extracted.eDC ;
    qs_edc            : 'qs Extracted.eDC ;
    hps_edc           : 'hps Extracted.eDC ;
    background_model  : (('v, 'hv, 'nv, 'vr, 'ts, 'fs, 'ps, 'ats, 'ms, 'qs, 'hps, 'prg) Extracted.backgroundModelOver) ;
    builtin_inject    : (builtin_repr -> 'v) ;
    builtin_eject     : ('v -> builtin_repr ) ;
    bindings          : (string -> ('ps, 'hps,'fs,'ats,'qs,'ms) Extracted.symbolInfo) ;
  }
