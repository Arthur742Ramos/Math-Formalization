/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.GeometryData0000
public import ErdosOverlap.Certificate.Native6Leaves.GeometryData0001
public import ErdosOverlap.Certificate.Native6Leaves.GeometryTraceData0000
public import ErdosOverlap.Certificate.Native6Leaves.PatchCheck0000
public import ErdosOverlap.Certificate.Native6Leaves.PatchCheck0001
public import ErdosOverlap.Certificate.Native6Leaves.PatchCheck0002
public import ErdosOverlap.Certificate.Native6Leaves.PatchCheck0003
public import ErdosOverlap.Numerics.NativePolynomialDirectTrace

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def checkedGeometry00000 : CheckedGeometry :=
  ⟨geometry00000, Geometry.check_of_directTraceCheck geometry00000
    checkedPatchCache0000 checkedPatchCache0001
    geometryTraceA00000 geometryTraceB00000 (by decide +kernel)⟩

def checkedGeometry00001 : CheckedGeometry :=
  ⟨geometry00001, Geometry.check_of_directTraceCheck geometry00001
    checkedPatchCache0002 checkedPatchCache0003
    geometryTraceA00001 geometryTraceB00001 (by decide +kernel)⟩

def checkedGeometry00002 : CheckedGeometry :=
  ⟨geometry00002, Geometry.check_of_directTraceCheck geometry00002
    checkedPatchCache0004 checkedPatchCache0005
    geometryTraceA00002 geometryTraceB00002 (by decide +kernel)⟩

def checkedGeometry00003 : CheckedGeometry :=
  ⟨geometry00003, Geometry.check_of_directTraceCheck geometry00003
    checkedPatchCache0006 checkedPatchCache0007
    geometryTraceA00003 geometryTraceB00003 (by decide +kernel)⟩

def checkedGeometry00004 : CheckedGeometry :=
  ⟨geometry00004, Geometry.check_of_directTraceCheck geometry00004
    checkedPatchCache0008 checkedPatchCache0009
    geometryTraceA00004 geometryTraceB00004 (by decide +kernel)⟩

def checkedGeometry00005 : CheckedGeometry :=
  ⟨geometry00005, Geometry.check_of_directTraceCheck geometry00005
    checkedPatchCache0010 checkedPatchCache0011
    geometryTraceA00005 geometryTraceB00005 (by decide +kernel)⟩

def checkedGeometry00006 : CheckedGeometry :=
  ⟨geometry00006, Geometry.check_of_directTraceCheck geometry00006
    checkedPatchCache0012 checkedPatchCache0013
    geometryTraceA00006 geometryTraceB00006 (by decide +kernel)⟩

def checkedGeometry00007 : CheckedGeometry :=
  ⟨geometry00007, Geometry.check_of_directTraceCheck geometry00007
    checkedPatchCache0014 checkedPatchCache0015
    geometryTraceA00007 geometryTraceB00007 (by decide +kernel)⟩

def checkedGeometry00008 : CheckedGeometry :=
  ⟨geometry00008, Geometry.check_of_directTraceCheck geometry00008
    checkedPatchCache0016 checkedPatchCache0017
    geometryTraceA00008 geometryTraceB00008 (by decide +kernel)⟩

def checkedGeometry00009 : CheckedGeometry :=
  ⟨geometry00009, Geometry.check_of_directTraceCheck geometry00009
    checkedPatchCache0018 checkedPatchCache0019
    geometryTraceA00009 geometryTraceB00009 (by decide +kernel)⟩

def checkedGeometry00010 : CheckedGeometry :=
  ⟨geometry00010, Geometry.check_of_directTraceCheck geometry00010
    checkedPatchCache0020 checkedPatchCache0021
    geometryTraceA00010 geometryTraceB00010 (by decide +kernel)⟩

def checkedGeometry00011 : CheckedGeometry :=
  ⟨geometry00011, Geometry.check_of_directTraceCheck geometry00011
    checkedPatchCache0022 checkedPatchCache0023
    geometryTraceA00011 geometryTraceB00011 (by decide +kernel)⟩

def checkedGeometry00012 : CheckedGeometry :=
  ⟨geometry00012, Geometry.check_of_directTraceCheck geometry00012
    checkedPatchCache0024 checkedPatchCache0025
    geometryTraceA00012 geometryTraceB00012 (by decide +kernel)⟩

def checkedGeometry00013 : CheckedGeometry :=
  ⟨geometry00013, Geometry.check_of_directTraceCheck geometry00013
    checkedPatchCache0026 checkedPatchCache0027
    geometryTraceA00013 geometryTraceB00013 (by decide +kernel)⟩

def checkedGeometry00014 : CheckedGeometry :=
  ⟨geometry00014, Geometry.check_of_directTraceCheck geometry00014
    checkedPatchCache0028 checkedPatchCache0029
    geometryTraceA00014 geometryTraceB00014 (by decide +kernel)⟩

def checkedGeometry00015 : CheckedGeometry :=
  ⟨geometry00015, Geometry.check_of_directTraceCheck geometry00015
    checkedPatchCache0030 checkedPatchCache0031
    geometryTraceA00015 geometryTraceB00015 (by decide +kernel)⟩

def checkedGeometry00016 : CheckedGeometry :=
  ⟨geometry00016, Geometry.check_of_directTraceCheck geometry00016
    checkedPatchCache0032 checkedPatchCache0033
    geometryTraceA00016 geometryTraceB00016 (by decide +kernel)⟩

def checkedGeometry00017 : CheckedGeometry :=
  ⟨geometry00017, Geometry.check_of_directTraceCheck geometry00017
    checkedPatchCache0034 checkedPatchCache0035
    geometryTraceA00017 geometryTraceB00017 (by decide +kernel)⟩

def checkedGeometry00018 : CheckedGeometry :=
  ⟨geometry00018, Geometry.check_of_directTraceCheck geometry00018
    checkedPatchCache0036 checkedPatchCache0037
    geometryTraceA00018 geometryTraceB00018 (by decide +kernel)⟩

def checkedGeometry00019 : CheckedGeometry :=
  ⟨geometry00019, Geometry.check_of_directTraceCheck geometry00019
    checkedPatchCache0038 checkedPatchCache0039
    geometryTraceA00019 geometryTraceB00019 (by decide +kernel)⟩

def checkedGeometry00020 : CheckedGeometry :=
  ⟨geometry00020, Geometry.check_of_directTraceCheck geometry00020
    checkedPatchCache0040 checkedPatchCache0041
    geometryTraceA00020 geometryTraceB00020 (by decide +kernel)⟩

def checkedGeometry00021 : CheckedGeometry :=
  ⟨geometry00021, Geometry.check_of_directTraceCheck geometry00021
    checkedPatchCache0042 checkedPatchCache0043
    geometryTraceA00021 geometryTraceB00021 (by decide +kernel)⟩

def checkedGeometry00022 : CheckedGeometry :=
  ⟨geometry00022, Geometry.check_of_directTraceCheck geometry00022
    checkedPatchCache0044 checkedPatchCache0045
    geometryTraceA00022 geometryTraceB00022 (by decide +kernel)⟩

def checkedGeometry00023 : CheckedGeometry :=
  ⟨geometry00023, Geometry.check_of_directTraceCheck geometry00023
    checkedPatchCache0046 checkedPatchCache0047
    geometryTraceA00023 geometryTraceB00023 (by decide +kernel)⟩

def checkedGeometry00024 : CheckedGeometry :=
  ⟨geometry00024, Geometry.check_of_directTraceCheck geometry00024
    checkedPatchCache0048 checkedPatchCache0049
    geometryTraceA00024 geometryTraceB00024 (by decide +kernel)⟩

def checkedGeometry00025 : CheckedGeometry :=
  ⟨geometry00025, Geometry.check_of_directTraceCheck geometry00025
    checkedPatchCache0050 checkedPatchCache0051
    geometryTraceA00025 geometryTraceB00025 (by decide +kernel)⟩

def checkedGeometry00026 : CheckedGeometry :=
  ⟨geometry00026, Geometry.check_of_directTraceCheck geometry00026
    checkedPatchCache0052 checkedPatchCache0053
    geometryTraceA00026 geometryTraceB00026 (by decide +kernel)⟩

def checkedGeometry00027 : CheckedGeometry :=
  ⟨geometry00027, Geometry.check_of_directTraceCheck geometry00027
    checkedPatchCache0054 checkedPatchCache0055
    geometryTraceA00027 geometryTraceB00027 (by decide +kernel)⟩

def checkedGeometry00028 : CheckedGeometry :=
  ⟨geometry00028, Geometry.check_of_directTraceCheck geometry00028
    checkedPatchCache0056 checkedPatchCache0057
    geometryTraceA00028 geometryTraceB00028 (by decide +kernel)⟩

def checkedGeometry00029 : CheckedGeometry :=
  ⟨geometry00029, Geometry.check_of_directTraceCheck geometry00029
    checkedPatchCache0058 checkedPatchCache0059
    geometryTraceA00029 geometryTraceB00029 (by decide +kernel)⟩

def checkedGeometry00030 : CheckedGeometry :=
  ⟨geometry00030, Geometry.check_of_directTraceCheck geometry00030
    checkedPatchCache0060 checkedPatchCache0061
    geometryTraceA00030 geometryTraceB00030 (by decide +kernel)⟩

def checkedGeometry00031 : CheckedGeometry :=
  ⟨geometry00031, Geometry.check_of_directTraceCheck geometry00031
    checkedPatchCache0062 checkedPatchCache0063
    geometryTraceA00031 geometryTraceB00031 (by decide +kernel)⟩

def checkedGeometry00032 : CheckedGeometry :=
  ⟨geometry00032, Geometry.check_of_directTraceCheck geometry00032
    checkedPatchCache0064 checkedPatchCache0065
    geometryTraceA00032 geometryTraceB00032 (by decide +kernel)⟩

def checkedGeometry00033 : CheckedGeometry :=
  ⟨geometry00033, Geometry.check_of_directTraceCheck geometry00033
    checkedPatchCache0066 checkedPatchCache0067
    geometryTraceA00033 geometryTraceB00033 (by decide +kernel)⟩

def checkedGeometry00034 : CheckedGeometry :=
  ⟨geometry00034, Geometry.check_of_directTraceCheck geometry00034
    checkedPatchCache0068 checkedPatchCache0069
    geometryTraceA00034 geometryTraceB00034 (by decide +kernel)⟩

def checkedGeometry00035 : CheckedGeometry :=
  ⟨geometry00035, Geometry.check_of_directTraceCheck geometry00035
    checkedPatchCache0070 checkedPatchCache0071
    geometryTraceA00035 geometryTraceB00035 (by decide +kernel)⟩

def checkedGeometry00036 : CheckedGeometry :=
  ⟨geometry00036, Geometry.check_of_directTraceCheck geometry00036
    checkedPatchCache0072 checkedPatchCache0073
    geometryTraceA00036 geometryTraceB00036 (by decide +kernel)⟩

def checkedGeometry00037 : CheckedGeometry :=
  ⟨geometry00037, Geometry.check_of_directTraceCheck geometry00037
    checkedPatchCache0074 checkedPatchCache0075
    geometryTraceA00037 geometryTraceB00037 (by decide +kernel)⟩

def checkedGeometry00038 : CheckedGeometry :=
  ⟨geometry00038, Geometry.check_of_directTraceCheck geometry00038
    checkedPatchCache0076 checkedPatchCache0077
    geometryTraceA00038 geometryTraceB00038 (by decide +kernel)⟩

def checkedGeometry00039 : CheckedGeometry :=
  ⟨geometry00039, Geometry.check_of_directTraceCheck geometry00039
    checkedPatchCache0078 checkedPatchCache0079
    geometryTraceA00039 geometryTraceB00039 (by decide +kernel)⟩

def checkedGeometry00040 : CheckedGeometry :=
  ⟨geometry00040, Geometry.check_of_directTraceCheck geometry00040
    checkedPatchCache0080 checkedPatchCache0081
    geometryTraceA00040 geometryTraceB00040 (by decide +kernel)⟩

def checkedGeometry00041 : CheckedGeometry :=
  ⟨geometry00041, Geometry.check_of_directTraceCheck geometry00041
    checkedPatchCache0082 checkedPatchCache0083
    geometryTraceA00041 geometryTraceB00041 (by decide +kernel)⟩

def checkedGeometry00042 : CheckedGeometry :=
  ⟨geometry00042, Geometry.check_of_directTraceCheck geometry00042
    checkedPatchCache0084 checkedPatchCache0085
    geometryTraceA00042 geometryTraceB00042 (by decide +kernel)⟩

def checkedGeometry00043 : CheckedGeometry :=
  ⟨geometry00043, Geometry.check_of_directTraceCheck geometry00043
    checkedPatchCache0086 checkedPatchCache0087
    geometryTraceA00043 geometryTraceB00043 (by decide +kernel)⟩

def checkedGeometry00044 : CheckedGeometry :=
  ⟨geometry00044, Geometry.check_of_directTraceCheck geometry00044
    checkedPatchCache0088 checkedPatchCache0089
    geometryTraceA00044 geometryTraceB00044 (by decide +kernel)⟩

def checkedGeometry00045 : CheckedGeometry :=
  ⟨geometry00045, Geometry.check_of_directTraceCheck geometry00045
    checkedPatchCache0090 checkedPatchCache0091
    geometryTraceA00045 geometryTraceB00045 (by decide +kernel)⟩

def checkedGeometry00046 : CheckedGeometry :=
  ⟨geometry00046, Geometry.check_of_directTraceCheck geometry00046
    checkedPatchCache0092 checkedPatchCache0093
    geometryTraceA00046 geometryTraceB00046 (by decide +kernel)⟩

def checkedGeometry00047 : CheckedGeometry :=
  ⟨geometry00047, Geometry.check_of_directTraceCheck geometry00047
    checkedPatchCache0094 checkedPatchCache0095
    geometryTraceA00047 geometryTraceB00047 (by decide +kernel)⟩

def checkedGeometry00048 : CheckedGeometry :=
  ⟨geometry00048, Geometry.check_of_directTraceCheck geometry00048
    checkedPatchCache0096 checkedPatchCache0097
    geometryTraceA00048 geometryTraceB00048 (by decide +kernel)⟩

def checkedGeometry00049 : CheckedGeometry :=
  ⟨geometry00049, Geometry.check_of_directTraceCheck geometry00049
    checkedPatchCache0098 checkedPatchCache0099
    geometryTraceA00049 geometryTraceB00049 (by decide +kernel)⟩

def checkedGeometry00050 : CheckedGeometry :=
  ⟨geometry00050, Geometry.check_of_directTraceCheck geometry00050
    checkedPatchCache0100 checkedPatchCache0101
    geometryTraceA00050 geometryTraceB00050 (by decide +kernel)⟩

def checkedGeometry00051 : CheckedGeometry :=
  ⟨geometry00051, Geometry.check_of_directTraceCheck geometry00051
    checkedPatchCache0102 checkedPatchCache0103
    geometryTraceA00051 geometryTraceB00051 (by decide +kernel)⟩

def checkedGeometry00052 : CheckedGeometry :=
  ⟨geometry00052, Geometry.check_of_directTraceCheck geometry00052
    checkedPatchCache0104 checkedPatchCache0105
    geometryTraceA00052 geometryTraceB00052 (by decide +kernel)⟩

def checkedGeometry00053 : CheckedGeometry :=
  ⟨geometry00053, Geometry.check_of_directTraceCheck geometry00053
    checkedPatchCache0106 checkedPatchCache0107
    geometryTraceA00053 geometryTraceB00053 (by decide +kernel)⟩

def checkedGeometry00054 : CheckedGeometry :=
  ⟨geometry00054, Geometry.check_of_directTraceCheck geometry00054
    checkedPatchCache0108 checkedPatchCache0109
    geometryTraceA00054 geometryTraceB00054 (by decide +kernel)⟩

def checkedGeometry00055 : CheckedGeometry :=
  ⟨geometry00055, Geometry.check_of_directTraceCheck geometry00055
    checkedPatchCache0110 checkedPatchCache0111
    geometryTraceA00055 geometryTraceB00055 (by decide +kernel)⟩

def checkedGeometry00056 : CheckedGeometry :=
  ⟨geometry00056, Geometry.check_of_directTraceCheck geometry00056
    checkedPatchCache0112 checkedPatchCache0113
    geometryTraceA00056 geometryTraceB00056 (by decide +kernel)⟩

def checkedGeometry00057 : CheckedGeometry :=
  ⟨geometry00057, Geometry.check_of_directTraceCheck geometry00057
    checkedPatchCache0114 checkedPatchCache0115
    geometryTraceA00057 geometryTraceB00057 (by decide +kernel)⟩

def checkedGeometry00058 : CheckedGeometry :=
  ⟨geometry00058, Geometry.check_of_directTraceCheck geometry00058
    checkedPatchCache0114 checkedPatchCache0115
    geometryTraceA00058 geometryTraceB00058 (by decide +kernel)⟩

def checkedGeometry00059 : CheckedGeometry :=
  ⟨geometry00059, Geometry.check_of_directTraceCheck geometry00059
    checkedPatchCache0114 checkedPatchCache0115
    geometryTraceA00059 geometryTraceB00059 (by decide +kernel)⟩

def checkedGeometry00060 : CheckedGeometry :=
  ⟨geometry00060, Geometry.check_of_directTraceCheck geometry00060
    checkedPatchCache0114 checkedPatchCache0115
    geometryTraceA00060 geometryTraceB00060 (by decide +kernel)⟩

def checkedGeometry00061 : CheckedGeometry :=
  ⟨geometry00061, Geometry.check_of_directTraceCheck geometry00061
    checkedPatchCache0114 checkedPatchCache0115
    geometryTraceA00061 geometryTraceB00061 (by decide +kernel)⟩

def checkedGeometry00062 : CheckedGeometry :=
  ⟨geometry00062, Geometry.check_of_directTraceCheck geometry00062
    checkedPatchCache0114 checkedPatchCache0115
    geometryTraceA00062 geometryTraceB00062 (by decide +kernel)⟩

def checkedGeometry00063 : CheckedGeometry :=
  ⟨geometry00063, Geometry.check_of_directTraceCheck geometry00063
    checkedPatchCache0114 checkedPatchCache0115
    geometryTraceA00063 geometryTraceB00063 (by decide +kernel)⟩

def checkedGeometry00064 : CheckedGeometry :=
  ⟨geometry00064, Geometry.check_of_directTraceCheck geometry00064
    checkedPatchCache0116 checkedPatchCache0117
    geometryTraceA00064 geometryTraceB00064 (by decide +kernel)⟩

def checkedGeometry00065 : CheckedGeometry :=
  ⟨geometry00065, Geometry.check_of_directTraceCheck geometry00065
    checkedPatchCache0116 checkedPatchCache0117
    geometryTraceA00065 geometryTraceB00065 (by decide +kernel)⟩

def checkedGeometry00066 : CheckedGeometry :=
  ⟨geometry00066, Geometry.check_of_directTraceCheck geometry00066
    checkedPatchCache0116 checkedPatchCache0117
    geometryTraceA00066 geometryTraceB00066 (by decide +kernel)⟩

def checkedGeometry00067 : CheckedGeometry :=
  ⟨geometry00067, Geometry.check_of_directTraceCheck geometry00067
    checkedPatchCache0116 checkedPatchCache0117
    geometryTraceA00067 geometryTraceB00067 (by decide +kernel)⟩

def checkedGeometry00068 : CheckedGeometry :=
  ⟨geometry00068, Geometry.check_of_directTraceCheck geometry00068
    checkedPatchCache0116 checkedPatchCache0117
    geometryTraceA00068 geometryTraceB00068 (by decide +kernel)⟩

def checkedGeometry00069 : CheckedGeometry :=
  ⟨geometry00069, Geometry.check_of_directTraceCheck geometry00069
    checkedPatchCache0116 checkedPatchCache0117
    geometryTraceA00069 geometryTraceB00069 (by decide +kernel)⟩

def checkedGeometry00070 : CheckedGeometry :=
  ⟨geometry00070, Geometry.check_of_directTraceCheck geometry00070
    checkedPatchCache0118 checkedPatchCache0119
    geometryTraceA00070 geometryTraceB00070 (by decide +kernel)⟩

def checkedGeometry00071 : CheckedGeometry :=
  ⟨geometry00071, Geometry.check_of_directTraceCheck geometry00071
    checkedPatchCache0118 checkedPatchCache0119
    geometryTraceA00071 geometryTraceB00071 (by decide +kernel)⟩

def checkedGeometry00072 : CheckedGeometry :=
  ⟨geometry00072, Geometry.check_of_directTraceCheck geometry00072
    checkedPatchCache0118 checkedPatchCache0119
    geometryTraceA00072 geometryTraceB00072 (by decide +kernel)⟩

def checkedGeometry00073 : CheckedGeometry :=
  ⟨geometry00073, Geometry.check_of_directTraceCheck geometry00073
    checkedPatchCache0118 checkedPatchCache0119
    geometryTraceA00073 geometryTraceB00073 (by decide +kernel)⟩

def checkedGeometry00074 : CheckedGeometry :=
  ⟨geometry00074, Geometry.check_of_directTraceCheck geometry00074
    checkedPatchCache0118 checkedPatchCache0119
    geometryTraceA00074 geometryTraceB00074 (by decide +kernel)⟩

def checkedGeometry00075 : CheckedGeometry :=
  ⟨geometry00075, Geometry.check_of_directTraceCheck geometry00075
    checkedPatchCache0118 checkedPatchCache0119
    geometryTraceA00075 geometryTraceB00075 (by decide +kernel)⟩

def checkedGeometry00076 : CheckedGeometry :=
  ⟨geometry00076, Geometry.check_of_directTraceCheck geometry00076
    checkedPatchCache0118 checkedPatchCache0119
    geometryTraceA00076 geometryTraceB00076 (by decide +kernel)⟩

def checkedGeometry00077 : CheckedGeometry :=
  ⟨geometry00077, Geometry.check_of_directTraceCheck geometry00077
    checkedPatchCache0120 checkedPatchCache0121
    geometryTraceA00077 geometryTraceB00077 (by decide +kernel)⟩

def checkedGeometry00078 : CheckedGeometry :=
  ⟨geometry00078, Geometry.check_of_directTraceCheck geometry00078
    checkedPatchCache0120 checkedPatchCache0121
    geometryTraceA00078 geometryTraceB00078 (by decide +kernel)⟩

def checkedGeometry00079 : CheckedGeometry :=
  ⟨geometry00079, Geometry.check_of_directTraceCheck geometry00079
    checkedPatchCache0120 checkedPatchCache0121
    geometryTraceA00079 geometryTraceB00079 (by decide +kernel)⟩

def checkedGeometry00080 : CheckedGeometry :=
  ⟨geometry00080, Geometry.check_of_directTraceCheck geometry00080
    checkedPatchCache0120 checkedPatchCache0121
    geometryTraceA00080 geometryTraceB00080 (by decide +kernel)⟩

def checkedGeometry00081 : CheckedGeometry :=
  ⟨geometry00081, Geometry.check_of_directTraceCheck geometry00081
    checkedPatchCache0120 checkedPatchCache0121
    geometryTraceA00081 geometryTraceB00081 (by decide +kernel)⟩

def checkedGeometry00082 : CheckedGeometry :=
  ⟨geometry00082, Geometry.check_of_directTraceCheck geometry00082
    checkedPatchCache0120 checkedPatchCache0121
    geometryTraceA00082 geometryTraceB00082 (by decide +kernel)⟩

def checkedGeometry00083 : CheckedGeometry :=
  ⟨geometry00083, Geometry.check_of_directTraceCheck geometry00083
    checkedPatchCache0120 checkedPatchCache0121
    geometryTraceA00083 geometryTraceB00083 (by decide +kernel)⟩

def checkedGeometry00084 : CheckedGeometry :=
  ⟨geometry00084, Geometry.check_of_directTraceCheck geometry00084
    checkedPatchCache0122 checkedPatchCache0123
    geometryTraceA00084 geometryTraceB00084 (by decide +kernel)⟩

def checkedGeometry00085 : CheckedGeometry :=
  ⟨geometry00085, Geometry.check_of_directTraceCheck geometry00085
    checkedPatchCache0122 checkedPatchCache0123
    geometryTraceA00085 geometryTraceB00085 (by decide +kernel)⟩

def checkedGeometry00086 : CheckedGeometry :=
  ⟨geometry00086, Geometry.check_of_directTraceCheck geometry00086
    checkedPatchCache0122 checkedPatchCache0123
    geometryTraceA00086 geometryTraceB00086 (by decide +kernel)⟩

def checkedGeometry00087 : CheckedGeometry :=
  ⟨geometry00087, Geometry.check_of_directTraceCheck geometry00087
    checkedPatchCache0122 checkedPatchCache0123
    geometryTraceA00087 geometryTraceB00087 (by decide +kernel)⟩

def checkedGeometry00088 : CheckedGeometry :=
  ⟨geometry00088, Geometry.check_of_directTraceCheck geometry00088
    checkedPatchCache0122 checkedPatchCache0123
    geometryTraceA00088 geometryTraceB00088 (by decide +kernel)⟩

def checkedGeometry00089 : CheckedGeometry :=
  ⟨geometry00089, Geometry.check_of_directTraceCheck geometry00089
    checkedPatchCache0122 checkedPatchCache0123
    geometryTraceA00089 geometryTraceB00089 (by decide +kernel)⟩

def checkedGeometry00090 : CheckedGeometry :=
  ⟨geometry00090, Geometry.check_of_directTraceCheck geometry00090
    checkedPatchCache0122 checkedPatchCache0123
    geometryTraceA00090 geometryTraceB00090 (by decide +kernel)⟩

def checkedGeometry00091 : CheckedGeometry :=
  ⟨geometry00091, Geometry.check_of_directTraceCheck geometry00091
    checkedPatchCache0124 checkedPatchCache0125
    geometryTraceA00091 geometryTraceB00091 (by decide +kernel)⟩

def checkedGeometry00092 : CheckedGeometry :=
  ⟨geometry00092, Geometry.check_of_directTraceCheck geometry00092
    checkedPatchCache0124 checkedPatchCache0125
    geometryTraceA00092 geometryTraceB00092 (by decide +kernel)⟩

def checkedGeometry00093 : CheckedGeometry :=
  ⟨geometry00093, Geometry.check_of_directTraceCheck geometry00093
    checkedPatchCache0124 checkedPatchCache0125
    geometryTraceA00093 geometryTraceB00093 (by decide +kernel)⟩

def checkedGeometry00094 : CheckedGeometry :=
  ⟨geometry00094, Geometry.check_of_directTraceCheck geometry00094
    checkedPatchCache0124 checkedPatchCache0125
    geometryTraceA00094 geometryTraceB00094 (by decide +kernel)⟩

def checkedGeometry00095 : CheckedGeometry :=
  ⟨geometry00095, Geometry.check_of_directTraceCheck geometry00095
    checkedPatchCache0124 checkedPatchCache0125
    geometryTraceA00095 geometryTraceB00095 (by decide +kernel)⟩

def checkedGeometry00096 : CheckedGeometry :=
  ⟨geometry00096, Geometry.check_of_directTraceCheck geometry00096
    checkedPatchCache0126 checkedPatchCache0127
    geometryTraceA00096 geometryTraceB00096 (by decide +kernel)⟩

def checkedGeometry00097 : CheckedGeometry :=
  ⟨geometry00097, Geometry.check_of_directTraceCheck geometry00097
    checkedPatchCache0126 checkedPatchCache0127
    geometryTraceA00097 geometryTraceB00097 (by decide +kernel)⟩

def checkedGeometry00098 : CheckedGeometry :=
  ⟨geometry00098, Geometry.check_of_directTraceCheck geometry00098
    checkedPatchCache0126 checkedPatchCache0127
    geometryTraceA00098 geometryTraceB00098 (by decide +kernel)⟩

def checkedGeometry00099 : CheckedGeometry :=
  ⟨geometry00099, Geometry.check_of_directTraceCheck geometry00099
    checkedPatchCache0126 checkedPatchCache0127
    geometryTraceA00099 geometryTraceB00099 (by decide +kernel)⟩

def checkedGeometry00100 : CheckedGeometry :=
  ⟨geometry00100, Geometry.check_of_directTraceCheck geometry00100
    checkedPatchCache0126 checkedPatchCache0127
    geometryTraceA00100 geometryTraceB00100 (by decide +kernel)⟩

def checkedGeometry00101 : CheckedGeometry :=
  ⟨geometry00101, Geometry.check_of_directTraceCheck geometry00101
    checkedPatchCache0126 checkedPatchCache0127
    geometryTraceA00101 geometryTraceB00101 (by decide +kernel)⟩

def checkedGeometry00102 : CheckedGeometry :=
  ⟨geometry00102, Geometry.check_of_directTraceCheck geometry00102
    checkedPatchCache0128 checkedPatchCache0129
    geometryTraceA00102 geometryTraceB00102 (by decide +kernel)⟩

def checkedGeometry00103 : CheckedGeometry :=
  ⟨geometry00103, Geometry.check_of_directTraceCheck geometry00103
    checkedPatchCache0130 checkedPatchCache0131
    geometryTraceA00103 geometryTraceB00103 (by decide +kernel)⟩

def checkedGeometry00104 : CheckedGeometry :=
  ⟨geometry00104, Geometry.check_of_directTraceCheck geometry00104
    checkedPatchCache0132 checkedPatchCache0133
    geometryTraceA00104 geometryTraceB00104 (by decide +kernel)⟩

def checkedGeometry00105 : CheckedGeometry :=
  ⟨geometry00105, Geometry.check_of_directTraceCheck geometry00105
    checkedPatchCache0134 checkedPatchCache0135
    geometryTraceA00105 geometryTraceB00105 (by decide +kernel)⟩

def checkedGeometry00106 : CheckedGeometry :=
  ⟨geometry00106, Geometry.check_of_directTraceCheck geometry00106
    checkedPatchCache0136 checkedPatchCache0137
    geometryTraceA00106 geometryTraceB00106 (by decide +kernel)⟩

def checkedGeometry00107 : CheckedGeometry :=
  ⟨geometry00107, Geometry.check_of_directTraceCheck geometry00107
    checkedPatchCache0138 checkedPatchCache0139
    geometryTraceA00107 geometryTraceB00107 (by decide +kernel)⟩

def checkedGeometry00108 : CheckedGeometry :=
  ⟨geometry00108, Geometry.check_of_directTraceCheck geometry00108
    checkedPatchCache0140 checkedPatchCache0141
    geometryTraceA00108 geometryTraceB00108 (by decide +kernel)⟩

def checkedGeometry00109 : CheckedGeometry :=
  ⟨geometry00109, Geometry.check_of_directTraceCheck geometry00109
    checkedPatchCache0142 checkedPatchCache0143
    geometryTraceA00109 geometryTraceB00109 (by decide +kernel)⟩

def checkedGeometry00110 : CheckedGeometry :=
  ⟨geometry00110, Geometry.check_of_directTraceCheck geometry00110
    checkedPatchCache0144 checkedPatchCache0145
    geometryTraceA00110 geometryTraceB00110 (by decide +kernel)⟩

def checkedGeometry00111 : CheckedGeometry :=
  ⟨geometry00111, Geometry.check_of_directTraceCheck geometry00111
    checkedPatchCache0146 checkedPatchCache0147
    geometryTraceA00111 geometryTraceB00111 (by decide +kernel)⟩

def checkedGeometry00112 : CheckedGeometry :=
  ⟨geometry00112, Geometry.check_of_directTraceCheck geometry00112
    checkedPatchCache0148 checkedPatchCache0149
    geometryTraceA00112 geometryTraceB00112 (by decide +kernel)⟩

def checkedGeometry00113 : CheckedGeometry :=
  ⟨geometry00113, Geometry.check_of_directTraceCheck geometry00113
    checkedPatchCache0150 checkedPatchCache0151
    geometryTraceA00113 geometryTraceB00113 (by decide +kernel)⟩

def checkedGeometry00114 : CheckedGeometry :=
  ⟨geometry00114, Geometry.check_of_directTraceCheck geometry00114
    checkedPatchCache0152 checkedPatchCache0153
    geometryTraceA00114 geometryTraceB00114 (by decide +kernel)⟩

def checkedGeometry00115 : CheckedGeometry :=
  ⟨geometry00115, Geometry.check_of_directTraceCheck geometry00115
    checkedPatchCache0154 checkedPatchCache0155
    geometryTraceA00115 geometryTraceB00115 (by decide +kernel)⟩

def checkedGeometry00116 : CheckedGeometry :=
  ⟨geometry00116, Geometry.check_of_directTraceCheck geometry00116
    checkedPatchCache0156 checkedPatchCache0157
    geometryTraceA00116 geometryTraceB00116 (by decide +kernel)⟩

def checkedGeometry00117 : CheckedGeometry :=
  ⟨geometry00117, Geometry.check_of_directTraceCheck geometry00117
    checkedPatchCache0158 checkedPatchCache0159
    geometryTraceA00117 geometryTraceB00117 (by decide +kernel)⟩

def checkedGeometry00118 : CheckedGeometry :=
  ⟨geometry00118, Geometry.check_of_directTraceCheck geometry00118
    checkedPatchCache0160 checkedPatchCache0161
    geometryTraceA00118 geometryTraceB00118 (by decide +kernel)⟩

def checkedGeometry00119 : CheckedGeometry :=
  ⟨geometry00119, Geometry.check_of_directTraceCheck geometry00119
    checkedPatchCache0162 checkedPatchCache0163
    geometryTraceA00119 geometryTraceB00119 (by decide +kernel)⟩

def checkedGeometry00120 : CheckedGeometry :=
  ⟨geometry00120, Geometry.check_of_directTraceCheck geometry00120
    checkedPatchCache0164 checkedPatchCache0165
    geometryTraceA00120 geometryTraceB00120 (by decide +kernel)⟩

def checkedGeometry00121 : CheckedGeometry :=
  ⟨geometry00121, Geometry.check_of_directTraceCheck geometry00121
    checkedPatchCache0166 checkedPatchCache0167
    geometryTraceA00121 geometryTraceB00121 (by decide +kernel)⟩

def checkedGeometry00122 : CheckedGeometry :=
  ⟨geometry00122, Geometry.check_of_directTraceCheck geometry00122
    checkedPatchCache0168 checkedPatchCache0169
    geometryTraceA00122 geometryTraceB00122 (by decide +kernel)⟩

def checkedGeometry00123 : CheckedGeometry :=
  ⟨geometry00123, Geometry.check_of_directTraceCheck geometry00123
    checkedPatchCache0170 checkedPatchCache0171
    geometryTraceA00123 geometryTraceB00123 (by decide +kernel)⟩

def checkedGeometry00124 : CheckedGeometry :=
  ⟨geometry00124, Geometry.check_of_directTraceCheck geometry00124
    checkedPatchCache0172 checkedPatchCache0173
    geometryTraceA00124 geometryTraceB00124 (by decide +kernel)⟩

def checkedGeometry00125 : CheckedGeometry :=
  ⟨geometry00125, Geometry.check_of_directTraceCheck geometry00125
    checkedPatchCache0174 checkedPatchCache0175
    geometryTraceA00125 geometryTraceB00125 (by decide +kernel)⟩

def checkedGeometry00126 : CheckedGeometry :=
  ⟨geometry00126, Geometry.check_of_directTraceCheck geometry00126
    checkedPatchCache0176 checkedPatchCache0177
    geometryTraceA00126 geometryTraceB00126 (by decide +kernel)⟩

def checkedGeometry00127 : CheckedGeometry :=
  ⟨geometry00127, Geometry.check_of_directTraceCheck geometry00127
    checkedPatchCache0178 checkedPatchCache0179
    geometryTraceA00127 geometryTraceB00127 (by decide +kernel)⟩

def checkedGeometry00128 : CheckedGeometry :=
  ⟨geometry00128, Geometry.check_of_directTraceCheck geometry00128
    checkedPatchCache0180 checkedPatchCache0181
    geometryTraceA00128 geometryTraceB00128 (by decide +kernel)⟩

def checkedGeometry00129 : CheckedGeometry :=
  ⟨geometry00129, Geometry.check_of_directTraceCheck geometry00129
    checkedPatchCache0182 checkedPatchCache0183
    geometryTraceA00129 geometryTraceB00129 (by decide +kernel)⟩

def checkedGeometry00130 : CheckedGeometry :=
  ⟨geometry00130, Geometry.check_of_directTraceCheck geometry00130
    checkedPatchCache0184 checkedPatchCache0185
    geometryTraceA00130 geometryTraceB00130 (by decide +kernel)⟩

def checkedGeometry00131 : CheckedGeometry :=
  ⟨geometry00131, Geometry.check_of_directTraceCheck geometry00131
    checkedPatchCache0186 checkedPatchCache0187
    geometryTraceA00131 geometryTraceB00131 (by decide +kernel)⟩

def checkedGeometry00132 : CheckedGeometry :=
  ⟨geometry00132, Geometry.check_of_directTraceCheck geometry00132
    checkedPatchCache0188 checkedPatchCache0189
    geometryTraceA00132 geometryTraceB00132 (by decide +kernel)⟩

def checkedGeometry00133 : CheckedGeometry :=
  ⟨geometry00133, Geometry.check_of_directTraceCheck geometry00133
    checkedPatchCache0190 checkedPatchCache0191
    geometryTraceA00133 geometryTraceB00133 (by decide +kernel)⟩

def checkedGeometry00134 : CheckedGeometry :=
  ⟨geometry00134, Geometry.check_of_directTraceCheck geometry00134
    checkedPatchCache0192 checkedPatchCache0193
    geometryTraceA00134 geometryTraceB00134 (by decide +kernel)⟩

def checkedGeometry00135 : CheckedGeometry :=
  ⟨geometry00135, Geometry.check_of_directTraceCheck geometry00135
    checkedPatchCache0194 checkedPatchCache0195
    geometryTraceA00135 geometryTraceB00135 (by decide +kernel)⟩

def checkedGeometry00136 : CheckedGeometry :=
  ⟨geometry00136, Geometry.check_of_directTraceCheck geometry00136
    checkedPatchCache0196 checkedPatchCache0197
    geometryTraceA00136 geometryTraceB00136 (by decide +kernel)⟩

def checkedGeometry00137 : CheckedGeometry :=
  ⟨geometry00137, Geometry.check_of_directTraceCheck geometry00137
    checkedPatchCache0198 checkedPatchCache0199
    geometryTraceA00137 geometryTraceB00137 (by decide +kernel)⟩

def checkedGeometry00138 : CheckedGeometry :=
  ⟨geometry00138, Geometry.check_of_directTraceCheck geometry00138
    checkedPatchCache0200 checkedPatchCache0201
    geometryTraceA00138 geometryTraceB00138 (by decide +kernel)⟩

def checkedGeometry00139 : CheckedGeometry :=
  ⟨geometry00139, Geometry.check_of_directTraceCheck geometry00139
    checkedPatchCache0202 checkedPatchCache0203
    geometryTraceA00139 geometryTraceB00139 (by decide +kernel)⟩

def checkedGeometry00140 : CheckedGeometry :=
  ⟨geometry00140, Geometry.check_of_directTraceCheck geometry00140
    checkedPatchCache0204 checkedPatchCache0205
    geometryTraceA00140 geometryTraceB00140 (by decide +kernel)⟩

def checkedGeometry00141 : CheckedGeometry :=
  ⟨geometry00141, Geometry.check_of_directTraceCheck geometry00141
    checkedPatchCache0206 checkedPatchCache0207
    geometryTraceA00141 geometryTraceB00141 (by decide +kernel)⟩

def checkedGeometry00142 : CheckedGeometry :=
  ⟨geometry00142, Geometry.check_of_directTraceCheck geometry00142
    checkedPatchCache0208 checkedPatchCache0209
    geometryTraceA00142 geometryTraceB00142 (by decide +kernel)⟩

def checkedGeometry00143 : CheckedGeometry :=
  ⟨geometry00143, Geometry.check_of_directTraceCheck geometry00143
    checkedPatchCache0210 checkedPatchCache0211
    geometryTraceA00143 geometryTraceB00143 (by decide +kernel)⟩

def checkedGeometry00144 : CheckedGeometry :=
  ⟨geometry00144, Geometry.check_of_directTraceCheck geometry00144
    checkedPatchCache0212 checkedPatchCache0213
    geometryTraceA00144 geometryTraceB00144 (by decide +kernel)⟩

def checkedGeometry00145 : CheckedGeometry :=
  ⟨geometry00145, Geometry.check_of_directTraceCheck geometry00145
    checkedPatchCache0214 checkedPatchCache0215
    geometryTraceA00145 geometryTraceB00145 (by decide +kernel)⟩

def checkedGeometry00146 : CheckedGeometry :=
  ⟨geometry00146, Geometry.check_of_directTraceCheck geometry00146
    checkedPatchCache0216 checkedPatchCache0217
    geometryTraceA00146 geometryTraceB00146 (by decide +kernel)⟩

def checkedGeometry00147 : CheckedGeometry :=
  ⟨geometry00147, Geometry.check_of_directTraceCheck geometry00147
    checkedPatchCache0218 checkedPatchCache0219
    geometryTraceA00147 geometryTraceB00147 (by decide +kernel)⟩

def checkedGeometry00148 : CheckedGeometry :=
  ⟨geometry00148, Geometry.check_of_directTraceCheck geometry00148
    checkedPatchCache0220 checkedPatchCache0221
    geometryTraceA00148 geometryTraceB00148 (by decide +kernel)⟩

def checkedGeometry00149 : CheckedGeometry :=
  ⟨geometry00149, Geometry.check_of_directTraceCheck geometry00149
    checkedPatchCache0222 checkedPatchCache0223
    geometryTraceA00149 geometryTraceB00149 (by decide +kernel)⟩

def checkedGeometry00150 : CheckedGeometry :=
  ⟨geometry00150, Geometry.check_of_directTraceCheck geometry00150
    checkedPatchCache0224 checkedPatchCache0225
    geometryTraceA00150 geometryTraceB00150 (by decide +kernel)⟩

def checkedGeometry00151 : CheckedGeometry :=
  ⟨geometry00151, Geometry.check_of_directTraceCheck geometry00151
    checkedPatchCache0226 checkedPatchCache0227
    geometryTraceA00151 geometryTraceB00151 (by decide +kernel)⟩

def checkedGeometry00152 : CheckedGeometry :=
  ⟨geometry00152, Geometry.check_of_directTraceCheck geometry00152
    checkedPatchCache0226 checkedPatchCache0227
    geometryTraceA00152 geometryTraceB00152 (by decide +kernel)⟩

def checkedGeometry00153 : CheckedGeometry :=
  ⟨geometry00153, Geometry.check_of_directTraceCheck geometry00153
    checkedPatchCache0226 checkedPatchCache0227
    geometryTraceA00153 geometryTraceB00153 (by decide +kernel)⟩

def checkedGeometry00154 : CheckedGeometry :=
  ⟨geometry00154, Geometry.check_of_directTraceCheck geometry00154
    checkedPatchCache0226 checkedPatchCache0227
    geometryTraceA00154 geometryTraceB00154 (by decide +kernel)⟩

def checkedGeometry00155 : CheckedGeometry :=
  ⟨geometry00155, Geometry.check_of_directTraceCheck geometry00155
    checkedPatchCache0226 checkedPatchCache0227
    geometryTraceA00155 geometryTraceB00155 (by decide +kernel)⟩

def checkedGeometry00156 : CheckedGeometry :=
  ⟨geometry00156, Geometry.check_of_directTraceCheck geometry00156
    checkedPatchCache0226 checkedPatchCache0227
    geometryTraceA00156 geometryTraceB00156 (by decide +kernel)⟩

def checkedGeometry00157 : CheckedGeometry :=
  ⟨geometry00157, Geometry.check_of_directTraceCheck geometry00157
    checkedPatchCache0226 checkedPatchCache0227
    geometryTraceA00157 geometryTraceB00157 (by decide +kernel)⟩

def checkedGeometry00158 : CheckedGeometry :=
  ⟨geometry00158, Geometry.check_of_directTraceCheck geometry00158
    checkedPatchCache0228 checkedPatchCache0229
    geometryTraceA00158 geometryTraceB00158 (by decide +kernel)⟩

def checkedGeometry00159 : CheckedGeometry :=
  ⟨geometry00159, Geometry.check_of_directTraceCheck geometry00159
    checkedPatchCache0228 checkedPatchCache0229
    geometryTraceA00159 geometryTraceB00159 (by decide +kernel)⟩

def checkedGeometry00160 : CheckedGeometry :=
  ⟨geometry00160, Geometry.check_of_directTraceCheck geometry00160
    checkedPatchCache0228 checkedPatchCache0229
    geometryTraceA00160 geometryTraceB00160 (by decide +kernel)⟩

def checkedGeometry00161 : CheckedGeometry :=
  ⟨geometry00161, Geometry.check_of_directTraceCheck geometry00161
    checkedPatchCache0228 checkedPatchCache0229
    geometryTraceA00161 geometryTraceB00161 (by decide +kernel)⟩

def checkedGeometry00162 : CheckedGeometry :=
  ⟨geometry00162, Geometry.check_of_directTraceCheck geometry00162
    checkedPatchCache0228 checkedPatchCache0229
    geometryTraceA00162 geometryTraceB00162 (by decide +kernel)⟩

def checkedGeometry00163 : CheckedGeometry :=
  ⟨geometry00163, Geometry.check_of_directTraceCheck geometry00163
    checkedPatchCache0228 checkedPatchCache0229
    geometryTraceA00163 geometryTraceB00163 (by decide +kernel)⟩

def checkedGeometry00164 : CheckedGeometry :=
  ⟨geometry00164, Geometry.check_of_directTraceCheck geometry00164
    checkedPatchCache0228 checkedPatchCache0229
    geometryTraceA00164 geometryTraceB00164 (by decide +kernel)⟩

def checkedGeometry00165 : CheckedGeometry :=
  ⟨geometry00165, Geometry.check_of_directTraceCheck geometry00165
    checkedPatchCache0228 checkedPatchCache0229
    geometryTraceA00165 geometryTraceB00165 (by decide +kernel)⟩

def checkedGeometry00166 : CheckedGeometry :=
  ⟨geometry00166, Geometry.check_of_directTraceCheck geometry00166
    checkedPatchCache0230 checkedPatchCache0231
    geometryTraceA00166 geometryTraceB00166 (by decide +kernel)⟩

def checkedGeometry00167 : CheckedGeometry :=
  ⟨geometry00167, Geometry.check_of_directTraceCheck geometry00167
    checkedPatchCache0230 checkedPatchCache0231
    geometryTraceA00167 geometryTraceB00167 (by decide +kernel)⟩

def checkedGeometry00168 : CheckedGeometry :=
  ⟨geometry00168, Geometry.check_of_directTraceCheck geometry00168
    checkedPatchCache0230 checkedPatchCache0231
    geometryTraceA00168 geometryTraceB00168 (by decide +kernel)⟩

def checkedGeometry00169 : CheckedGeometry :=
  ⟨geometry00169, Geometry.check_of_directTraceCheck geometry00169
    checkedPatchCache0230 checkedPatchCache0231
    geometryTraceA00169 geometryTraceB00169 (by decide +kernel)⟩

def checkedGeometry00170 : CheckedGeometry :=
  ⟨geometry00170, Geometry.check_of_directTraceCheck geometry00170
    checkedPatchCache0230 checkedPatchCache0231
    geometryTraceA00170 geometryTraceB00170 (by decide +kernel)⟩

def checkedGeometry00171 : CheckedGeometry :=
  ⟨geometry00171, Geometry.check_of_directTraceCheck geometry00171
    checkedPatchCache0230 checkedPatchCache0231
    geometryTraceA00171 geometryTraceB00171 (by decide +kernel)⟩

def checkedGeometry00172 : CheckedGeometry :=
  ⟨geometry00172, Geometry.check_of_directTraceCheck geometry00172
    checkedPatchCache0230 checkedPatchCache0231
    geometryTraceA00172 geometryTraceB00172 (by decide +kernel)⟩

def checkedGeometry00173 : CheckedGeometry :=
  ⟨geometry00173, Geometry.check_of_directTraceCheck geometry00173
    checkedPatchCache0230 checkedPatchCache0231
    geometryTraceA00173 geometryTraceB00173 (by decide +kernel)⟩

def checkedGeometry00174 : CheckedGeometry :=
  ⟨geometry00174, Geometry.check_of_directTraceCheck geometry00174
    checkedPatchCache0232 checkedPatchCache0233
    geometryTraceA00174 geometryTraceB00174 (by decide +kernel)⟩

def checkedGeometry00175 : CheckedGeometry :=
  ⟨geometry00175, Geometry.check_of_directTraceCheck geometry00175
    checkedPatchCache0232 checkedPatchCache0233
    geometryTraceA00175 geometryTraceB00175 (by decide +kernel)⟩

def checkedGeometry00176 : CheckedGeometry :=
  ⟨geometry00176, Geometry.check_of_directTraceCheck geometry00176
    checkedPatchCache0232 checkedPatchCache0233
    geometryTraceA00176 geometryTraceB00176 (by decide +kernel)⟩

def checkedGeometry00177 : CheckedGeometry :=
  ⟨geometry00177, Geometry.check_of_directTraceCheck geometry00177
    checkedPatchCache0232 checkedPatchCache0233
    geometryTraceA00177 geometryTraceB00177 (by decide +kernel)⟩

def checkedGeometry00178 : CheckedGeometry :=
  ⟨geometry00178, Geometry.check_of_directTraceCheck geometry00178
    checkedPatchCache0232 checkedPatchCache0233
    geometryTraceA00178 geometryTraceB00178 (by decide +kernel)⟩

def checkedGeometry00179 : CheckedGeometry :=
  ⟨geometry00179, Geometry.check_of_directTraceCheck geometry00179
    checkedPatchCache0232 checkedPatchCache0233
    geometryTraceA00179 geometryTraceB00179 (by decide +kernel)⟩

def checkedGeometry00180 : CheckedGeometry :=
  ⟨geometry00180, Geometry.check_of_directTraceCheck geometry00180
    checkedPatchCache0232 checkedPatchCache0233
    geometryTraceA00180 geometryTraceB00180 (by decide +kernel)⟩

def checkedGeometry00181 : CheckedGeometry :=
  ⟨geometry00181, Geometry.check_of_directTraceCheck geometry00181
    checkedPatchCache0234 checkedPatchCache0235
    geometryTraceA00181 geometryTraceB00181 (by decide +kernel)⟩

def checkedGeometry00182 : CheckedGeometry :=
  ⟨geometry00182, Geometry.check_of_directTraceCheck geometry00182
    checkedPatchCache0234 checkedPatchCache0235
    geometryTraceA00182 geometryTraceB00182 (by decide +kernel)⟩

def checkedGeometry00183 : CheckedGeometry :=
  ⟨geometry00183, Geometry.check_of_directTraceCheck geometry00183
    checkedPatchCache0234 checkedPatchCache0235
    geometryTraceA00183 geometryTraceB00183 (by decide +kernel)⟩

def checkedGeometry00184 : CheckedGeometry :=
  ⟨geometry00184, Geometry.check_of_directTraceCheck geometry00184
    checkedPatchCache0234 checkedPatchCache0235
    geometryTraceA00184 geometryTraceB00184 (by decide +kernel)⟩

def checkedGeometry00185 : CheckedGeometry :=
  ⟨geometry00185, Geometry.check_of_directTraceCheck geometry00185
    checkedPatchCache0234 checkedPatchCache0235
    geometryTraceA00185 geometryTraceB00185 (by decide +kernel)⟩

def checkedGeometry00186 : CheckedGeometry :=
  ⟨geometry00186, Geometry.check_of_directTraceCheck geometry00186
    checkedPatchCache0234 checkedPatchCache0235
    geometryTraceA00186 geometryTraceB00186 (by decide +kernel)⟩

def checkedGeometry00187 : CheckedGeometry :=
  ⟨geometry00187, Geometry.check_of_directTraceCheck geometry00187
    checkedPatchCache0234 checkedPatchCache0235
    geometryTraceA00187 geometryTraceB00187 (by decide +kernel)⟩

def checkedGeometry00188 : CheckedGeometry :=
  ⟨geometry00188, Geometry.check_of_directTraceCheck geometry00188
    checkedPatchCache0234 checkedPatchCache0235
    geometryTraceA00188 geometryTraceB00188 (by decide +kernel)⟩

def checkedGeometry00189 : CheckedGeometry :=
  ⟨geometry00189, Geometry.check_of_directTraceCheck geometry00189
    checkedPatchCache0236 checkedPatchCache0237
    geometryTraceA00189 geometryTraceB00189 (by decide +kernel)⟩

def checkedGeometry00190 : CheckedGeometry :=
  ⟨geometry00190, Geometry.check_of_directTraceCheck geometry00190
    checkedPatchCache0236 checkedPatchCache0237
    geometryTraceA00190 geometryTraceB00190 (by decide +kernel)⟩

def checkedGeometry00191 : CheckedGeometry :=
  ⟨geometry00191, Geometry.check_of_directTraceCheck geometry00191
    checkedPatchCache0236 checkedPatchCache0237
    geometryTraceA00191 geometryTraceB00191 (by decide +kernel)⟩

def checkedGeometry00192 : CheckedGeometry :=
  ⟨geometry00192, Geometry.check_of_directTraceCheck geometry00192
    checkedPatchCache0236 checkedPatchCache0237
    geometryTraceA00192 geometryTraceB00192 (by decide +kernel)⟩

def checkedGeometry00193 : CheckedGeometry :=
  ⟨geometry00193, Geometry.check_of_directTraceCheck geometry00193
    checkedPatchCache0236 checkedPatchCache0237
    geometryTraceA00193 geometryTraceB00193 (by decide +kernel)⟩

def checkedGeometry00194 : CheckedGeometry :=
  ⟨geometry00194, Geometry.check_of_directTraceCheck geometry00194
    checkedPatchCache0236 checkedPatchCache0237
    geometryTraceA00194 geometryTraceB00194 (by decide +kernel)⟩

def checkedGeometry00195 : CheckedGeometry :=
  ⟨geometry00195, Geometry.check_of_directTraceCheck geometry00195
    checkedPatchCache0236 checkedPatchCache0237
    geometryTraceA00195 geometryTraceB00195 (by decide +kernel)⟩

def checkedGeometry00196 : CheckedGeometry :=
  ⟨geometry00196, Geometry.check_of_directTraceCheck geometry00196
    checkedPatchCache0236 checkedPatchCache0237
    geometryTraceA00196 geometryTraceB00196 (by decide +kernel)⟩

def checkedGeometry00197 : CheckedGeometry :=
  ⟨geometry00197, Geometry.check_of_directTraceCheck geometry00197
    checkedPatchCache0238 checkedPatchCache0239
    geometryTraceA00197 geometryTraceB00197 (by decide +kernel)⟩

def checkedGeometry00198 : CheckedGeometry :=
  ⟨geometry00198, Geometry.check_of_directTraceCheck geometry00198
    checkedPatchCache0238 checkedPatchCache0239
    geometryTraceA00198 geometryTraceB00198 (by decide +kernel)⟩

def checkedGeometry00199 : CheckedGeometry :=
  ⟨geometry00199, Geometry.check_of_directTraceCheck geometry00199
    checkedPatchCache0238 checkedPatchCache0239
    geometryTraceA00199 geometryTraceB00199 (by decide +kernel)⟩

def checkedGeometry00200 : CheckedGeometry :=
  ⟨geometry00200, Geometry.check_of_directTraceCheck geometry00200
    checkedPatchCache0238 checkedPatchCache0239
    geometryTraceA00200 geometryTraceB00200 (by decide +kernel)⟩

def checkedGeometry00201 : CheckedGeometry :=
  ⟨geometry00201, Geometry.check_of_directTraceCheck geometry00201
    checkedPatchCache0238 checkedPatchCache0239
    geometryTraceA00201 geometryTraceB00201 (by decide +kernel)⟩

def checkedGeometry00202 : CheckedGeometry :=
  ⟨geometry00202, Geometry.check_of_directTraceCheck geometry00202
    checkedPatchCache0238 checkedPatchCache0239
    geometryTraceA00202 geometryTraceB00202 (by decide +kernel)⟩

def checkedGeometry00203 : CheckedGeometry :=
  ⟨geometry00203, Geometry.check_of_directTraceCheck geometry00203
    checkedPatchCache0238 checkedPatchCache0239
    geometryTraceA00203 geometryTraceB00203 (by decide +kernel)⟩

def checkedGeometry00204 : CheckedGeometry :=
  ⟨geometry00204, Geometry.check_of_directTraceCheck geometry00204
    checkedPatchCache0238 checkedPatchCache0239
    geometryTraceA00204 geometryTraceB00204 (by decide +kernel)⟩

def checkedGeometry00205 : CheckedGeometry :=
  ⟨geometry00205, Geometry.check_of_directTraceCheck geometry00205
    checkedPatchCache0238 checkedPatchCache0239
    geometryTraceA00205 geometryTraceB00205 (by decide +kernel)⟩

def checkedGeometry00206 : CheckedGeometry :=
  ⟨geometry00206, Geometry.check_of_directTraceCheck geometry00206
    checkedPatchCache0240 checkedPatchCache0241
    geometryTraceA00206 geometryTraceB00206 (by decide +kernel)⟩

def checkedGeometry00207 : CheckedGeometry :=
  ⟨geometry00207, Geometry.check_of_directTraceCheck geometry00207
    checkedPatchCache0240 checkedPatchCache0241
    geometryTraceA00207 geometryTraceB00207 (by decide +kernel)⟩

def checkedGeometry00208 : CheckedGeometry :=
  ⟨geometry00208, Geometry.check_of_directTraceCheck geometry00208
    checkedPatchCache0240 checkedPatchCache0241
    geometryTraceA00208 geometryTraceB00208 (by decide +kernel)⟩

def checkedGeometry00209 : CheckedGeometry :=
  ⟨geometry00209, Geometry.check_of_directTraceCheck geometry00209
    checkedPatchCache0240 checkedPatchCache0241
    geometryTraceA00209 geometryTraceB00209 (by decide +kernel)⟩

def checkedGeometry00210 : CheckedGeometry :=
  ⟨geometry00210, Geometry.check_of_directTraceCheck geometry00210
    checkedPatchCache0240 checkedPatchCache0241
    geometryTraceA00210 geometryTraceB00210 (by decide +kernel)⟩

def checkedGeometry00211 : CheckedGeometry :=
  ⟨geometry00211, Geometry.check_of_directTraceCheck geometry00211
    checkedPatchCache0240 checkedPatchCache0241
    geometryTraceA00211 geometryTraceB00211 (by decide +kernel)⟩

def checkedGeometry00212 : CheckedGeometry :=
  ⟨geometry00212, Geometry.check_of_directTraceCheck geometry00212
    checkedPatchCache0240 checkedPatchCache0241
    geometryTraceA00212 geometryTraceB00212 (by decide +kernel)⟩

def checkedGeometry00213 : CheckedGeometry :=
  ⟨geometry00213, Geometry.check_of_directTraceCheck geometry00213
    checkedPatchCache0240 checkedPatchCache0241
    geometryTraceA00213 geometryTraceB00213 (by decide +kernel)⟩

def checkedGeometry00214 : CheckedGeometry :=
  ⟨geometry00214, Geometry.check_of_directTraceCheck geometry00214
    checkedPatchCache0240 checkedPatchCache0241
    geometryTraceA00214 geometryTraceB00214 (by decide +kernel)⟩

def checkedGeometry00215 : CheckedGeometry :=
  ⟨geometry00215, Geometry.check_of_directTraceCheck geometry00215
    checkedPatchCache0242 checkedPatchCache0243
    geometryTraceA00215 geometryTraceB00215 (by decide +kernel)⟩

def checkedGeometry00216 : CheckedGeometry :=
  ⟨geometry00216, Geometry.check_of_directTraceCheck geometry00216
    checkedPatchCache0242 checkedPatchCache0243
    geometryTraceA00216 geometryTraceB00216 (by decide +kernel)⟩

def checkedGeometry00217 : CheckedGeometry :=
  ⟨geometry00217, Geometry.check_of_directTraceCheck geometry00217
    checkedPatchCache0242 checkedPatchCache0243
    geometryTraceA00217 geometryTraceB00217 (by decide +kernel)⟩

def checkedGeometry00218 : CheckedGeometry :=
  ⟨geometry00218, Geometry.check_of_directTraceCheck geometry00218
    checkedPatchCache0242 checkedPatchCache0243
    geometryTraceA00218 geometryTraceB00218 (by decide +kernel)⟩

def checkedGeometry00219 : CheckedGeometry :=
  ⟨geometry00219, Geometry.check_of_directTraceCheck geometry00219
    checkedPatchCache0242 checkedPatchCache0243
    geometryTraceA00219 geometryTraceB00219 (by decide +kernel)⟩

def checkedGeometry00220 : CheckedGeometry :=
  ⟨geometry00220, Geometry.check_of_directTraceCheck geometry00220
    checkedPatchCache0242 checkedPatchCache0243
    geometryTraceA00220 geometryTraceB00220 (by decide +kernel)⟩

def checkedGeometry00221 : CheckedGeometry :=
  ⟨geometry00221, Geometry.check_of_directTraceCheck geometry00221
    checkedPatchCache0242 checkedPatchCache0243
    geometryTraceA00221 geometryTraceB00221 (by decide +kernel)⟩

def checkedGeometry00222 : CheckedGeometry :=
  ⟨geometry00222, Geometry.check_of_directTraceCheck geometry00222
    checkedPatchCache0242 checkedPatchCache0243
    geometryTraceA00222 geometryTraceB00222 (by decide +kernel)⟩

def checkedGeometry00223 : CheckedGeometry :=
  ⟨geometry00223, Geometry.check_of_directTraceCheck geometry00223
    checkedPatchCache0244 checkedPatchCache0245
    geometryTraceA00223 geometryTraceB00223 (by decide +kernel)⟩

def checkedGeometry00224 : CheckedGeometry :=
  ⟨geometry00224, Geometry.check_of_directTraceCheck geometry00224
    checkedPatchCache0244 checkedPatchCache0245
    geometryTraceA00224 geometryTraceB00224 (by decide +kernel)⟩

def checkedGeometry00225 : CheckedGeometry :=
  ⟨geometry00225, Geometry.check_of_directTraceCheck geometry00225
    checkedPatchCache0244 checkedPatchCache0245
    geometryTraceA00225 geometryTraceB00225 (by decide +kernel)⟩

def checkedGeometry00226 : CheckedGeometry :=
  ⟨geometry00226, Geometry.check_of_directTraceCheck geometry00226
    checkedPatchCache0244 checkedPatchCache0245
    geometryTraceA00226 geometryTraceB00226 (by decide +kernel)⟩

def checkedGeometry00227 : CheckedGeometry :=
  ⟨geometry00227, Geometry.check_of_directTraceCheck geometry00227
    checkedPatchCache0244 checkedPatchCache0245
    geometryTraceA00227 geometryTraceB00227 (by decide +kernel)⟩

def checkedGeometry00228 : CheckedGeometry :=
  ⟨geometry00228, Geometry.check_of_directTraceCheck geometry00228
    checkedPatchCache0244 checkedPatchCache0245
    geometryTraceA00228 geometryTraceB00228 (by decide +kernel)⟩

def checkedGeometry00229 : CheckedGeometry :=
  ⟨geometry00229, Geometry.check_of_directTraceCheck geometry00229
    checkedPatchCache0244 checkedPatchCache0245
    geometryTraceA00229 geometryTraceB00229 (by decide +kernel)⟩

def checkedGeometry00230 : CheckedGeometry :=
  ⟨geometry00230, Geometry.check_of_directTraceCheck geometry00230
    checkedPatchCache0244 checkedPatchCache0245
    geometryTraceA00230 geometryTraceB00230 (by decide +kernel)⟩

def checkedGeometry00231 : CheckedGeometry :=
  ⟨geometry00231, Geometry.check_of_directTraceCheck geometry00231
    checkedPatchCache0244 checkedPatchCache0245
    geometryTraceA00231 geometryTraceB00231 (by decide +kernel)⟩

def checkedGeometry00232 : CheckedGeometry :=
  ⟨geometry00232, Geometry.check_of_directTraceCheck geometry00232
    checkedPatchCache0246 checkedPatchCache0247
    geometryTraceA00232 geometryTraceB00232 (by decide +kernel)⟩

def checkedGeometry00233 : CheckedGeometry :=
  ⟨geometry00233, Geometry.check_of_directTraceCheck geometry00233
    checkedPatchCache0246 checkedPatchCache0247
    geometryTraceA00233 geometryTraceB00233 (by decide +kernel)⟩

def checkedGeometry00234 : CheckedGeometry :=
  ⟨geometry00234, Geometry.check_of_directTraceCheck geometry00234
    checkedPatchCache0246 checkedPatchCache0247
    geometryTraceA00234 geometryTraceB00234 (by decide +kernel)⟩

def checkedGeometry00235 : CheckedGeometry :=
  ⟨geometry00235, Geometry.check_of_directTraceCheck geometry00235
    checkedPatchCache0246 checkedPatchCache0247
    geometryTraceA00235 geometryTraceB00235 (by decide +kernel)⟩

def checkedGeometry00236 : CheckedGeometry :=
  ⟨geometry00236, Geometry.check_of_directTraceCheck geometry00236
    checkedPatchCache0246 checkedPatchCache0247
    geometryTraceA00236 geometryTraceB00236 (by decide +kernel)⟩

def checkedGeometry00237 : CheckedGeometry :=
  ⟨geometry00237, Geometry.check_of_directTraceCheck geometry00237
    checkedPatchCache0246 checkedPatchCache0247
    geometryTraceA00237 geometryTraceB00237 (by decide +kernel)⟩

def checkedGeometry00238 : CheckedGeometry :=
  ⟨geometry00238, Geometry.check_of_directTraceCheck geometry00238
    checkedPatchCache0246 checkedPatchCache0247
    geometryTraceA00238 geometryTraceB00238 (by decide +kernel)⟩

def checkedGeometry00239 : CheckedGeometry :=
  ⟨geometry00239, Geometry.check_of_directTraceCheck geometry00239
    checkedPatchCache0246 checkedPatchCache0247
    geometryTraceA00239 geometryTraceB00239 (by decide +kernel)⟩

def checkedGeometry00240 : CheckedGeometry :=
  ⟨geometry00240, Geometry.check_of_directTraceCheck geometry00240
    checkedPatchCache0246 checkedPatchCache0247
    geometryTraceA00240 geometryTraceB00240 (by decide +kernel)⟩

def checkedGeometry00241 : CheckedGeometry :=
  ⟨geometry00241, Geometry.check_of_directTraceCheck geometry00241
    checkedPatchCache0248 checkedPatchCache0249
    geometryTraceA00241 geometryTraceB00241 (by decide +kernel)⟩

def checkedGeometry00242 : CheckedGeometry :=
  ⟨geometry00242, Geometry.check_of_directTraceCheck geometry00242
    checkedPatchCache0248 checkedPatchCache0249
    geometryTraceA00242 geometryTraceB00242 (by decide +kernel)⟩

def checkedGeometry00243 : CheckedGeometry :=
  ⟨geometry00243, Geometry.check_of_directTraceCheck geometry00243
    checkedPatchCache0248 checkedPatchCache0249
    geometryTraceA00243 geometryTraceB00243 (by decide +kernel)⟩

def checkedGeometry00244 : CheckedGeometry :=
  ⟨geometry00244, Geometry.check_of_directTraceCheck geometry00244
    checkedPatchCache0248 checkedPatchCache0249
    geometryTraceA00244 geometryTraceB00244 (by decide +kernel)⟩

def checkedGeometry00245 : CheckedGeometry :=
  ⟨geometry00245, Geometry.check_of_directTraceCheck geometry00245
    checkedPatchCache0248 checkedPatchCache0249
    geometryTraceA00245 geometryTraceB00245 (by decide +kernel)⟩

def checkedGeometry00246 : CheckedGeometry :=
  ⟨geometry00246, Geometry.check_of_directTraceCheck geometry00246
    checkedPatchCache0248 checkedPatchCache0249
    geometryTraceA00246 geometryTraceB00246 (by decide +kernel)⟩

def checkedGeometry00247 : CheckedGeometry :=
  ⟨geometry00247, Geometry.check_of_directTraceCheck geometry00247
    checkedPatchCache0248 checkedPatchCache0249
    geometryTraceA00247 geometryTraceB00247 (by decide +kernel)⟩

def checkedGeometry00248 : CheckedGeometry :=
  ⟨geometry00248, Geometry.check_of_directTraceCheck geometry00248
    checkedPatchCache0248 checkedPatchCache0249
    geometryTraceA00248 geometryTraceB00248 (by decide +kernel)⟩

def checkedGeometry00249 : CheckedGeometry :=
  ⟨geometry00249, Geometry.check_of_directTraceCheck geometry00249
    checkedPatchCache0250 checkedPatchCache0251
    geometryTraceA00249 geometryTraceB00249 (by decide +kernel)⟩

def checkedGeometry00250 : CheckedGeometry :=
  ⟨geometry00250, Geometry.check_of_directTraceCheck geometry00250
    checkedPatchCache0250 checkedPatchCache0251
    geometryTraceA00250 geometryTraceB00250 (by decide +kernel)⟩

def checkedGeometry00251 : CheckedGeometry :=
  ⟨geometry00251, Geometry.check_of_directTraceCheck geometry00251
    checkedPatchCache0250 checkedPatchCache0251
    geometryTraceA00251 geometryTraceB00251 (by decide +kernel)⟩

def checkedGeometry00252 : CheckedGeometry :=
  ⟨geometry00252, Geometry.check_of_directTraceCheck geometry00252
    checkedPatchCache0250 checkedPatchCache0251
    geometryTraceA00252 geometryTraceB00252 (by decide +kernel)⟩

def checkedGeometry00253 : CheckedGeometry :=
  ⟨geometry00253, Geometry.check_of_directTraceCheck geometry00253
    checkedPatchCache0250 checkedPatchCache0251
    geometryTraceA00253 geometryTraceB00253 (by decide +kernel)⟩

def checkedGeometry00254 : CheckedGeometry :=
  ⟨geometry00254, Geometry.check_of_directTraceCheck geometry00254
    checkedPatchCache0250 checkedPatchCache0251
    geometryTraceA00254 geometryTraceB00254 (by decide +kernel)⟩

def checkedGeometry00255 : CheckedGeometry :=
  ⟨geometry00255, Geometry.check_of_directTraceCheck geometry00255
    checkedPatchCache0250 checkedPatchCache0251
    geometryTraceA00255 geometryTraceB00255 (by decide +kernel)⟩


end
end ErdosOverlap.Native6Leaves
