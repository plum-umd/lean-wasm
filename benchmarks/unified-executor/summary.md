# Unified executor benchmark

Hardware: Apple M1.
Toolchain: Lean (version 4.27.0, arm64-apple-darwin24.6.0, commit db93fe1608548721853390a10cd40580fe7d22ae, Release).

Both policies use the same explicit machine and fuel loop. Native policy adds
float/host extensions and call-depth limits; these workloads need no native ops.
Cells report fresh-process medians after one discarded warm-up per case/policy.
Execution excludes setup and boundary conversions; total includes both conversions.

| Policy | Workload | Iterations | Depth | Execution ms | Total ms | Execution range ms |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| certified | allocate | 1000 | 0 | 3.839 | 3.850 | 3.777–5.521 |
| native | allocate | 1000 | 0 | 3.916 | 3.926 | 3.843–4.893 |
| certified | allocate | 4000 | 0 | 15.093 | 15.123 | 14.994–15.227 |
| native | allocate | 4000 | 0 | 15.464 | 15.492 | 15.377–15.758 |
| certified | allocate | 16000 | 0 | 60.426 | 60.559 | 60.242–60.655 |
| native | allocate | 16000 | 0 | 61.424 | 61.564 | 61.235–61.749 |
| certified | allocate-read | 1000 | 0 | 4.628 | 4.638 | 4.576–4.675 |
| native | allocate-read | 1000 | 0 | 4.684 | 4.694 | 4.636–4.893 |
| certified | allocate-read | 4000 | 0 | 18.328 | 18.355 | 18.239–18.520 |
| native | allocate-read | 4000 | 0 | 18.585 | 18.617 | 18.427–18.650 |
| certified | allocate-read | 16000 | 0 | 73.367 | 73.498 | 73.039–73.435 |
| native | allocate-read | 16000 | 0 | 73.982 | 74.111 | 73.791–74.225 |
| certified | linked | 1000 | 0 | 15.316 | 15.325 | 15.294–15.409 |
| native | linked | 1000 | 0 | 15.611 | 15.620 | 15.492–16.050 |
| certified | linked | 4000 | 0 | 61.687 | 61.726 | 61.439–61.729 |
| native | linked | 4000 | 0 | 62.618 | 62.664 | 62.231–62.893 |
| certified | linked | 16000 | 0 | 253.630 | 253.829 | 246.982–259.073 |
| native | linked | 16000 | 0 | 253.927 | 254.109 | 249.818–257.806 |
| certified | read-early | 1000 | 0 | 3.830 | 3.848 | 3.807–4.127 |
| native | read-early | 1000 | 0 | 3.914 | 3.931 | 3.850–4.077 |
| certified | read-early | 4000 | 0 | 15.280 | 15.345 | 15.177–15.376 |
| native | read-early | 4000 | 0 | 15.388 | 15.455 | 15.204–15.937 |
| certified | read-early | 16000 | 0 | 75.986 | 76.321 | 62.770–108.025 |
| native | read-early | 16000 | 0 | 76.207 | 76.745 | 63.685–104.324 |
| certified | read-middle | 1000 | 0 | 3.839 | 3.855 | 3.806–4.206 |
| native | read-middle | 1000 | 0 | 3.900 | 3.917 | 3.837–4.025 |
| certified | read-middle | 4000 | 0 | 15.345 | 15.413 | 15.114–15.773 |
| native | read-middle | 4000 | 0 | 15.606 | 15.675 | 15.220–16.437 |
| certified | read-middle | 16000 | 0 | 64.094 | 64.354 | 62.376–84.833 |
| native | read-middle | 16000 | 0 | 66.257 | 66.519 | 63.429–80.445 |
| certified | read-late | 1000 | 0 | 3.951 | 3.968 | 3.930–4.343 |
| native | read-late | 1000 | 0 | 4.003 | 4.021 | 3.979–4.271 |
| certified | read-late | 4000 | 0 | 15.313 | 15.382 | 15.228–15.850 |
| native | read-late | 4000 | 0 | 15.394 | 15.466 | 15.324–15.937 |
| certified | read-late | 16000 | 0 | 62.975 | 63.243 | 60.862–80.924 |
| native | read-late | 16000 | 0 | 82.357 | 82.613 | 61.060–109.350 |
| certified | control | 1000 | 0 | 4.098 | 4.100 | 3.993–8.865 |
| native | control | 1000 | 0 | 4.302 | 4.304 | 4.042–4.760 |
| certified | control | 4000 | 0 | 15.868 | 15.869 | 15.715–16.272 |
| native | control | 4000 | 0 | 16.074 | 16.076 | 15.886–16.153 |
| certified | control | 16000 | 0 | 63.315 | 63.316 | 63.219–63.629 |
| native | control | 16000 | 0 | 63.903 | 63.904 | 63.767–65.711 |
| certified | blocks | 1000 | 0 | 4.013 | 4.014 | 3.931–4.141 |
| native | blocks | 1000 | 0 | 4.024 | 4.025 | 3.962–4.205 |
| certified | blocks | 1000 | 4 | 3.984 | 3.985 | 3.950–4.089 |
| native | blocks | 1000 | 4 | 4.004 | 4.005 | 3.982–4.096 |
| certified | blocks | 1000 | 16 | 3.959 | 3.960 | 3.940–4.088 |
| native | blocks | 1000 | 16 | 3.988 | 3.988 | 3.964–4.058 |
| certified | blocks | 1000 | 64 | 3.978 | 3.979 | 3.945–4.079 |
| native | blocks | 1000 | 64 | 4.014 | 4.015 | 3.975–4.079 |
| certified | blocks | 1000 | 256 | 4.097 | 4.097 | 4.066–4.149 |
| native | blocks | 1000 | 256 | 4.121 | 4.122 | 4.101–4.199 |
| certified | calls | 1000 | 0 | 3.966 | 3.967 | 3.953–4.029 |
| native | calls | 1000 | 0 | 4.004 | 4.005 | 3.977–4.136 |
| certified | calls | 1000 | 4 | 3.977 | 3.978 | 3.940–4.056 |
| native | calls | 1000 | 4 | 3.968 | 3.969 | 3.944–4.025 |
| certified | calls | 1000 | 16 | 4.035 | 4.036 | 4.008–4.150 |
| native | calls | 1000 | 16 | 4.077 | 4.078 | 4.045–4.117 |
| certified | calls | 1000 | 64 | 4.066 | 4.067 | 4.032–4.147 |
| native | calls | 1000 | 64 | 4.098 | 4.099 | 4.071–4.144 |
| certified | calls | 1000 | 256 | 4.574 | 4.575 | 4.513–4.643 |
| native | calls | 1000 | 256 | 4.737 | 4.739 | 4.685–4.802 |
| certified | tail-calls | 1000 | 0 | 4.049 | 4.050 | 3.937–4.116 |
| native | tail-calls | 1000 | 0 | 4.057 | 4.058 | 4.033–4.151 |
| certified | tail-calls | 1000 | 4 | 4.035 | 4.036 | 4.014–4.079 |
| native | tail-calls | 1000 | 4 | 4.069 | 4.070 | 4.059–4.149 |
| certified | tail-calls | 1000 | 16 | 3.996 | 3.996 | 3.957–4.041 |
| native | tail-calls | 1000 | 16 | 4.107 | 4.108 | 4.027–4.166 |
| certified | tail-calls | 1000 | 64 | 4.049 | 4.050 | 4.010–4.086 |
| native | tail-calls | 1000 | 64 | 4.086 | 4.087 | 4.065–4.128 |
| certified | tail-calls | 1000 | 256 | 4.437 | 4.438 | 4.418–4.837 |
| native | tail-calls | 1000 | 256 | 4.502 | 4.502 | 4.479–4.560 |
| certified | handlers | 1000 | 0 | 3.932 | 3.933 | 3.921–4.478 |
| native | handlers | 1000 | 0 | 3.984 | 3.985 | 3.969–4.123 |
| certified | handlers | 1000 | 4 | 4.016 | 4.018 | 3.979–4.110 |
| native | handlers | 1000 | 4 | 4.029 | 4.030 | 3.997–4.160 |
| certified | handlers | 1000 | 16 | 3.929 | 3.930 | 3.870–4.050 |
| native | handlers | 1000 | 16 | 4.030 | 4.030 | 3.929–4.138 |
| certified | handlers | 1000 | 64 | 3.926 | 3.927 | 3.913–3.972 |
| native | handlers | 1000 | 64 | 3.998 | 3.998 | 3.950–4.046 |
| certified | handlers | 1000 | 256 | 4.165 | 4.166 | 4.120–4.210 |
| native | handlers | 1000 | 256 | 4.192 | 4.193 | 4.152–4.297 |
| certified | unwind | 1000 | 0 | 3.876 | 3.877 | 3.870–4.071 |
| native | unwind | 1000 | 0 | 3.953 | 3.954 | 3.912–4.061 |
| certified | unwind | 1000 | 4 | 3.931 | 3.932 | 3.894–4.109 |
| native | unwind | 1000 | 4 | 3.955 | 3.956 | 3.939–4.158 |
| certified | unwind | 1000 | 16 | 3.892 | 3.893 | 3.858–3.932 |
| native | unwind | 1000 | 16 | 3.961 | 3.962 | 3.937–4.027 |
| certified | unwind | 1000 | 64 | 3.939 | 3.939 | 3.898–3.966 |
| native | unwind | 1000 | 64 | 3.961 | 3.962 | 3.951–4.115 |
| certified | unwind | 1000 | 256 | 4.133 | 4.134 | 4.108–4.184 |
| native | unwind | 1000 | 256 | 4.166 | 4.167 | 4.148–4.196 |
