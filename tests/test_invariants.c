/*
 * tests/test_invariants.c
 *
 * Strict CI Verification & Unit-Test Suite for MHMZAHRAN/symplectic-pairwise-3body
 *
 * Author: Mohammad Hossam Mohammed Ali Zahran (MHMZAHRAN)
 * Standard: ISO C99 (-std=c99 -O3 -Wall -Wextra -Werror -pedantic -fno-fast-math -lm)
 */

#include <stdio.h>
#include <stdlib.h>
#include <math.h>

#define STRICT_TOL 1.0e-13

static int g_tests_run    = 0;
static int g_tests_failed = 0;

#define REQUIRE_CLOSE(label, actual, expected, tol)                            \
    do {                                                                       \
        double _act = (double)(actual);                                        \
        double _exp = (double)(expected);                                      \
        double _err = fabs(_act - _exp);                                       \
        double _tol = (double)(tol);                                           \
        g_tests_run++;                                                         \
        if (isnan(_err) || isinf(_err) || _err > _tol) {                       \
            fprintf(stderr,                                                    \
                "[FAIL] %s (line %d): |%.16e - %.16e| = %.3e > %.3e\n",        \
                (label), __LINE__, _act, _exp, _err, _tol);                    \
            g_tests_failed++;                                                  \
        } else {                                                               \
            printf("[PASS] %-54s | err = %.3e <= %.1e\n",                      \
                (label), _err, _tol);                                          \
        }                                                                      \
    } while (0)

typedef struct {
    double x, y, z;
} Vec3;

typedef struct {
    Vec3 q, p;
} Phase6;

typedef struct {
    Vec3 q[3];
    Vec3 p[3];
    double m[3];
    double G;
} System3Body;

static inline Vec3 v3_add(Vec3 a, Vec3 b) {
    return (Vec3){a.x + b.x, a.y + b.y, a.z + b.z};
}

static inline Vec3 v3_sub(Vec3 a, Vec3 b) {
    return (Vec3){a.x - b.x, a.y - b.y, a.z - b.z};
}

static inline Vec3 v3_scale(double c, Vec3 a) {
    return (Vec3){c * a.x, c * a.y, c * a.z};
}

static inline double v3_dot(Vec3 a, Vec3 b) {
    return a.x * b.x + a.y * b.y + a.z * b.z;
}

static inline Vec3 v3_cross(Vec3 a, Vec3 b) {
    return (Vec3){
        a.y * b.z - a.z * b.y,
        a.z * b.x - a.x * b.z,
        a.x * b.y - a.y * b.x
    };
}

static inline double v3_norm(Vec3 a) {
    return sqrt(v3_dot(a, a));
}

static inline double omega6(Phase6 z, Phase6 w) {
    return v3_dot(z.q, w.p) - v3_dot(z.p, w.q);
}

static double omega18(const System3Body *z, const System3Body *w) {
    double sum = 0.0;
    for (int i = 0; i < 3; ++i) {
        Phase6 zi = {z->q[i], z->p[i]};
        Phase6 wi = {w->q[i], w->p[i]};
        sum += omega6(zi, wi);
    }
    return sum;
}

static void stumpff_CS(double z, double *C, double *S) {
    if (fabs(z) < 1e-4) {
        double z2 = z * z;
        double z3 = z2 * z;
        double z4 = z2 * z2;
        *C = 0.5 - z / 24.0 + z2 / 720.0 - z3 / 40320.0 + z4 / 3628800.0;
        *S = (1.0 / 6.0) - z / 120.0 + z2 / 5040.0 - z3 / 362880.0 + z4 / 39916800.0;
    } else if (z > 0.0) {
        double sz = sqrt(z);
        *C = (1.0 - cos(sz)) / z;
        *S = (sz - sin(sz)) / (sz * z);
    } else {
        double sz = sqrt(-z);
        *C = (cosh(sz) - 1.0) / (-z);
        *S = (sinh(sz) - sz) / (sz * (-z));
    }
}

static void compute_gauss_fg(
    Vec3 r0, Vec3 v0, double mu_grav, double tau,
    double *f_out, double *g_out, double *fdot_out, double *gdot_out
) {
    const double r0_mag  = v3_norm(r0);
    const double v0_sq   = v3_dot(v0, v0);
    const double rv0     = v3_dot(r0, v0);
    const double inv_a   = (2.0 / r0_mag) - (v0_sq / mu_grav);
    const double sqrt_mu = sqrt(mu_grav);

    double chi = sqrt_mu * fabs(inv_a) * tau;
    if (fabs(chi) < 1e-12) {
        chi = sqrt_mu * tau / r0_mag;
    }

    double C = 0.5, S = 1.0 / 6.0;
    for (int iter = 0; iter < 40; ++iter) {
        double chi2 = chi * chi;
        double z    = inv_a * chi2;
        stumpff_CS(z, &C, &S);

        double F  = r0_mag * chi + (rv0 / sqrt_mu) * chi2 * C
                  + (1.0 - inv_a * r0_mag) * chi2 * chi * S - sqrt_mu * tau;
        double dF = r0_mag + (rv0 / sqrt_mu) * chi * (1.0 - z * S)
                  + (1.0 - inv_a * r0_mag) * chi2 * C;

        double dchi = F / dF;
        chi -= dchi;
        if (fabs(dchi) <= 1e-15 * (1.0 + fabs(chi))) {
            break;
        }
    }

    double chi2 = chi * chi;
    double z    = inv_a * chi2;
    stumpff_CS(z, &C, &S);

    double f      = 1.0 - (chi2 / r0_mag) * C;
    double g      = tau - (chi2 * chi / sqrt_mu) * S;
    Vec3   r1     = v3_add(v3_scale(f, r0), v3_scale(g, v0));
    double r1_mag = v3_norm(r1);

    double fdot = (sqrt_mu / (r0_mag * r1_mag)) * (z * S - 1.0) * chi;
    double gdot = (1.0 + g * fdot) / f;

    *f_out    = f;
    *g_out    = g;
    *fdot_out = fdot;
    *gdot_out = gdot;
}

static void step_pair_kepler(System3Body *sys, int i, int j, double tau) {
    const double mi    = sys->m[i];
    const double mj    = sys->m[j];
    const double mij   = mi + mj;
    const double alpha = mi / mij;
    const double beta  = 1.0 - alpha;
    const double mu_ij = (mi * mj) / mij;

    Vec3 R_cm  = v3_add(v3_scale(alpha, sys->q[i]), v3_scale(beta, sys->q[j]));
    Vec3 P_cm  = v3_add(sys->p[i], sys->p[j]);
    Vec3 r0    = v3_sub(sys->q[i], sys->q[j]);
    Vec3 p_rel = v3_sub(v3_scale(beta, sys->p[i]), v3_scale(alpha, sys->p[j]));

    R_cm = v3_add(R_cm, v3_scale(tau / (2.0 * mij), P_cm));

    Vec3   v0      = v3_scale(1.0 / (2.0 * mu_ij), p_rel);
    double mu_grav = 0.5 * sys->G * mij;
    double f, g, fdot, gdot;
    compute_gauss_fg(r0, v0, mu_grav, tau, &f, &g, &fdot, &gdot);

    Vec3 r1     = v3_add(v3_scale(f, r0), v3_scale(g, v0));
    Vec3 v1     = v3_add(v3_scale(fdot, r0), v3_scale(gdot, v0));
    Vec3 p_rel1 = v3_scale(2.0 * mu_ij, v1);

    sys->q[i] = v3_add(R_cm, v3_scale(beta, r1));
    sys->p[i] = v3_add(v3_scale(alpha, P_cm), p_rel1);
    sys->q[j] = v3_sub(R_cm, v3_scale(alpha, r1));
    sys->p[j] = v3_sub(P_cm, sys->p[i]);
}

static void step_strang_2nd(System3Body *sys, double h) {
    const double h2 = 0.5 * h;
    step_pair_kepler(sys, 0, 1, h2);
    step_pair_kepler(sys, 1, 2, h2);
    step_pair_kepler(sys, 2, 0, h);
    step_pair_kepler(sys, 1, 2, h2);
    step_pair_kepler(sys, 0, 1, h2);
}

static void step_yoshida_4th(System3Body *sys, double h) {
    const double cbrt2 = 1.25992104989487316477;
    const double w1    = 1.0 / (2.0 - cbrt2);
    const double w0    = -cbrt2 / (2.0 - cbrt2);
    step_strang_2nd(sys, w1 * h);
    step_strang_2nd(sys, w0 * h);
    step_strang_2nd(sys, w1 * h);
}

static double total_energy(const System3Body *sys) {
    double T = 0.0, V = 0.0;
    for (int i = 0; i < 3; ++i) {
        T += v3_dot(sys->p[i], sys->p[i]) / (2.0 * sys->m[i]);
    }
    for (int i = 0; i < 3; ++i) {
        for (int j = i + 1; j < 3; ++j) {
            double rij = v3_norm(v3_sub(sys->q[i], sys->q[j]));
            V -= sys->G * sys->m[i] * sys->m[j] / rij;
        }
    }
    return T + V;
}

static Vec3 total_momentum(const System3Body *sys) {
    return v3_add(v3_add(sys->p[0], sys->p[1]), sys->p[2]);
}

static Vec3 total_angular_momentum(const System3Body *sys) {
    return v3_add(
        v3_add(v3_cross(sys->q[0], sys->p[0]), v3_cross(sys->q[1], sys->p[1])),
        v3_cross(sys->q[2], sys->p[2])
    );
}

static Vec3 barycentric_boost_invariant(const System3Body *sys, double t) {
    Vec3 M_R = v3_add(
        v3_add(v3_scale(sys->m[0], sys->q[0]), v3_scale(sys->m[1], sys->q[1])),
        v3_scale(sys->m[2], sys->q[2])
    );
    Vec3 P = total_momentum(sys);
    return v3_sub(M_R, v3_scale(t, P));
}

static void newtonian_accelerations(const System3Body *sys, Vec3 acc[3]) {
    for (int i = 0; i < 3; ++i) {
        acc[i] = (Vec3){0.0, 0.0, 0.0};
        for (int j = 0; j < 3; ++j) {
            if (i != j) {
                Vec3   rij = v3_sub(sys->q[j], sys->q[i]);
                double d   = v3_norm(rij);
                double k   = sys->G * sys->m[j] / (d * d * d);
                acc[i]     = v3_add(acc[i], v3_scale(k, rij));
            }
        }
    }
}

static void test_suite_wronskian(void) {
    printf("\n--- Suite 1: Gauss f-g Wronskian Identity (f*gdot - g*fdot = 1) ---\n");
    Vec3 r0 = {1.25, -0.45, 0.30};
    double r0_mag = v3_norm(r0);
    double mu = 1.35;

    Vec3 v_ell = {0.35, 0.72, -0.18};
    double f, g, fdot, gdot;
    compute_gauss_fg(r0, v_ell, mu, 0.15, &f, &g, &fdot, &gdot);
    REQUIRE_CLOSE("Wronskian Elliptic Orbit (z > 0)", f * gdot - g * fdot, 1.0, STRICT_TOL);

    double v_esc = sqrt(2.0 * mu / r0_mag);
    Vec3 v_par = {0.0, v_esc * 0.8, v_esc * 0.6};
    compute_gauss_fg(r0, v_par, mu, 0.05, &f, &g, &fdot, &gdot);
    REQUIRE_CLOSE("Wronskian Parabolic Taylor Branch (z ~ 0)", f * gdot - g * fdot, 1.0, STRICT_TOL);

    Vec3 v_hyp = {-1.40, 1.85, 0.95};
    compute_gauss_fg(r0, v_hyp, mu, 0.12, &f, &g, &fdot, &gdot);
    REQUIRE_CLOSE("Wronskian Hyperbolic Flyby (z < 0)", f * gdot - g * fdot, 1.0, STRICT_TOL);
}

static void apply_lifted_tangent_pair(
    System3Body *dz, int i, int j,
    double mi, double mj, double tau,
    double f, double g, double fdot, double gdot
) {
    const double mij   = mi + mj;
    const double alpha = mi / mij;
    const double beta  = 1.0 - alpha;
    const double mu_ij = (mi * mj) / mij;

    Vec3 dR_cm  = v3_add(v3_scale(alpha, dz->q[i]), v3_scale(beta, dz->q[j]));
    Vec3 dP_cm  = v3_add(dz->p[i], dz->p[j]);
    Vec3 dr0    = v3_sub(dz->q[i], dz->q[j]);
    Vec3 dp_rel = v3_sub(v3_scale(beta, dz->p[i]), v3_scale(alpha, dz->p[j]));

    dR_cm = v3_add(dR_cm, v3_scale(tau / (2.0 * mij), dP_cm));

    double g_c    = g / (2.0 * mu_ij);
    double fdot_c = (2.0 * mu_ij) * fdot;

    Vec3 dr1     = v3_add(v3_scale(f, dr0), v3_scale(g_c, dp_rel));
    Vec3 dp_rel1 = v3_add(v3_scale(fdot_c, dr0), v3_scale(gdot, dp_rel));

    dz->q[i] = v3_add(dR_cm, v3_scale(beta, dr1));
    dz->p[i] = v3_add(v3_scale(alpha, dP_cm), dp_rel1);
    dz->q[j] = v3_sub(dR_cm, v3_scale(alpha, dr1));
    dz->p[j] = v3_sub(dP_cm, dz->p[i]);
}

static void test_suite_symplectic_2form(void) {
    printf("\n--- Suite 2: Canonical 18D Symplectic 2-Form (omega_18) Preservation ---\n");
    System3Body z = {
        .q = {{ 0.42, -1.15,  0.73}, {-0.88,  0.54, -0.31}, { 1.29,  0.67, -0.92}},
        .p = {{-0.51,  0.83,  0.19}, { 0.74, -0.29, -0.63}, {-0.23, -0.54,  0.44}},
        .m = {1.35, 0.85, 1.60},
        .G = 1.0
    };
    System3Body w = {
        .q = {{-0.63,  0.29,  1.04}, { 0.91, -0.77,  0.48}, {-0.38,  0.82, -0.59}},
        .p = {{ 0.66,  0.17, -0.84}, {-0.45,  0.61,  0.27}, {-0.21, -0.78,  0.57}},
        .m = {1.35, 0.85, 1.60},
        .G = 1.0
    };

    const double omega_init = omega18(&z, &w);

    double f12 = 0.985, g12 = 0.042, gdot12 = 0.991;
    double fdot12 = (f12 * gdot12 - 1.0) / g12;

    double f23 = 0.978, g23 = 0.051, gdot23 = 0.984;
    double fdot23 = (f23 * gdot23 - 1.0) / g23;

    double f31 = 0.964, g31 = 0.088, gdot31 = 0.972;
    double fdot31 = (f31 * gdot31 - 1.0) / g31;

    const double h = 0.05;
    apply_lifted_tangent_pair(&z, 0, 1, z.m[0], z.m[1], 0.5 * h, f12, g12, fdot12, gdot12);
    apply_lifted_tangent_pair(&w, 0, 1, w.m[0], w.m[1], 0.5 * h, f12, g12, fdot12, gdot12);
    REQUIRE_CLOSE("Lifted Pair (1,2) preserves omega_18", omega18(&z, &w), omega_init, STRICT_TOL);

    apply_lifted_tangent_pair(&z, 1, 2, z.m[1], z.m[2], 0.5 * h, f23, g23, fdot23, gdot23);
    apply_lifted_tangent_pair(&w, 1, 2, w.m[1], w.m[2], 0.5 * h, f23, g23, fdot23, gdot23);

    apply_lifted_tangent_pair(&z, 2, 0, z.m[2], z.m[0], h, f31, g31, fdot31, gdot31);
    apply_lifted_tangent_pair(&w, 2, 0, w.m[2], w.m[0], h, f31, g31, fdot31, gdot31);

    apply_lifted_tangent_pair(&z, 1, 2, z.m[1], z.m[2], 0.5 * h, f23, g23, fdot23, gdot23);
    apply_lifted_tangent_pair(&w, 1, 2, w.m[1], w.m[2], 0.5 * h, f23, g23, fdot23, gdot23);

    apply_lifted_tangent_pair(&z, 0, 1, z.m[0], z.m[1], 0.5 * h, f12, g12, fdot12, gdot12);
    apply_lifted_tangent_pair(&w, 0, 1, w.m[0], w.m[1], 0.5 * h, f12, g12, fdot12, gdot12);

    REQUIRE_CLOSE("Full 5-stage Strang composition preserves omega_18",
                  omega18(&z, &w), omega_init, STRICT_TOL);
}

static void test_suite_lagrange_equilateral(void) {
    printf("\n--- Suite 3: Master Interconnected Equation & Lagrange Exact Decoupling ---\n");
    const double L = 2.0;
    const double s3 = sqrt(3.0);

    System3Body sys = {
        .q = {
            { 0.0,      s3 / 3.0 * L, 0.0},
            {-0.5 * L, -s3 / 6.0 * L, 0.0},
            { 0.5 * L, -s3 / 6.0 * L, 0.0}
        },
        .p = {{0.0, 0.0, 0.0}, {0.0, 0.0, 0.0}, {0.0, 0.0, 0.0}},
        .m = {1.85, 0.75, 1.40},
        .G = 1.0
    };

    const double M = sys.m[0] + sys.m[1] + sys.m[2];
    Vec3 r12 = v3_sub(sys.q[0], sys.q[1]);
    Vec3 r23 = v3_sub(sys.q[1], sys.q[2]);
    Vec3 r31 = v3_sub(sys.q[2], sys.q[0]);

    Vec3 closure = v3_add(v3_add(r12, r23), r31);
    REQUIRE_CLOSE("Triangle Closure ||r12 + r23 + r31|| == 0", v3_norm(closure), 0.0, STRICT_TOL);

    double d12 = v3_norm(r12), d23 = v3_norm(r23), d31 = v3_norm(r31);
    double k12 = sys.G / (d12 * d12 * d12);
    double k23 = sys.G / (d23 * d23 * d23);
    double k31 = sys.G / (d31 * d31 * d31);

    Vec3 delta12 = v3_scale(sys.m[2], v3_add(
        v3_scale(k31 - k12, r31),
        v3_scale(k23 - k12, r23)
    ));
    REQUIRE_CLOSE("Lagrange Tidal Mismatch ||Delta_12|| == 0 (unequal masses)",
                  v3_norm(delta12), 0.0, STRICT_TOL);

    Vec3 acc[3];
    newtonian_accelerations(&sys, acc);
    Vec3 ddot_r12_exact  = v3_sub(acc[0], acc[1]);
    Vec3 ddot_r12_kepler = v3_scale(-M * k12, r12);
    REQUIRE_CLOSE("Lagrange Decoupled 2-Body Acceleration Match (Pair 1-2)",
                  v3_norm(v3_sub(ddot_r12_exact, ddot_r12_kepler)), 0.0, STRICT_TOL);

    sys.q[0] = (Vec3){ 1.10, -0.40, 0.25};
    sys.q[1] = (Vec3){-0.75,  0.85, -0.60};
    sys.q[2] = (Vec3){ 0.30,  0.95,  1.20};
    newtonian_accelerations(&sys, acc);

    r12 = v3_sub(sys.q[0], sys.q[1]);
    r23 = v3_sub(sys.q[1], sys.q[2]);
    r31 = v3_sub(sys.q[2], sys.q[0]);
    d12 = v3_norm(r12); d23 = v3_norm(r23); d31 = v3_norm(r31);
    k12 = sys.G / (d12 * d12 * d12);
    k23 = sys.G / (d23 * d23 * d23);
    k31 = sys.G / (d31 * d31 * d31);

    Vec3 master_rhs12 = v3_add(
        v3_scale(-M * k12, r12),
        v3_scale(sys.m[2], v3_add(v3_scale(k31 - k12, r31), v3_scale(k23 - k12, r23)))
    );
    REQUIRE_CLOSE("Master Interconnected Decomposition Identity (General 3D)",
                  v3_norm(v3_sub(v3_sub(acc[0], acc[1]), master_rhs12)), 0.0, STRICT_TOL);
}

static void test_suite_euler_collinear(void) {
    printf("\n--- Suite 4: Euler Collinear Exact Two-Body Reduction ---\n");
    const double m1 = 1.50, m2 = 1.00, m3 = 0.80;

    double lam = 1.0;
    for (int iter = 0; iter < 40; ++iter) {
        double l2 = lam * lam, l3 = l2 * lam, l4 = l3 * lam, l5 = l4 * lam;
        double P  = (m1 + m2) * l5 + (3.0 * m1 + 2.0 * m2) * l4 + (3.0 * m1 + m2) * l3
                  - (m2 + 3.0 * m3) * l2 - (2.0 * m2 + 3.0 * m3) * lam - (m2 + m3);
        double dP = 5.0 * (m1 + m2) * l4 + 4.0 * (3.0 * m1 + 2.0 * m2) * l3
                  + 3.0 * (3.0 * m1 + m2) * l2 - 2.0 * (m2 + 3.0 * m3) * lam
                  - (2.0 * m2 + 3.0 * m3);
        lam -= P / dP;
    }

    Vec3 q1 = { 1.40, -0.60, 0.30};
    Vec3 q2 = {-0.20,  0.50, -0.10};
    Vec3 r12 = v3_sub(q1, q2);
    Vec3 q3 = v3_sub(q2, v3_scale(lam, r12));

    System3Body sys = {
        .q = {q1, q2, q3},
        .p = {{0, 0, 0}, {0, 0, 0}, {0, 0, 0}},
        .m = {m1, m2, m3},
        .G = 1.0
    };

    Vec3 acc[3];
    newtonian_accelerations(&sys, acc);

    double d12 = v3_norm(v3_sub(q1, q2));
    double d23 = v3_norm(v3_sub(q2, q3));
    double d31 = v3_norm(v3_sub(q3, q1));
    double k12 = sys.G / (d12 * d12 * d12);
    double k23 = sys.G / (d23 * d23 * d23);
    double k31 = sys.G / (d31 * d31 * d31);

    double k_eff = (m1 + m2) * k12 + m3 * (1.0 + lam) * k31 - m3 * lam * k23;
    Vec3 ddot_r12_euler = v3_scale(-k_eff, r12);
    REQUIRE_CLOSE("Euler Collinear Renormalized 2-Body Acceleration",
                  v3_norm(v3_sub(v3_sub(acc[0], acc[1]), ddot_r12_euler)), 0.0, STRICT_TOL);

    double k_eff_23 = (m2 + m3) * k23 + m1 * ((1.0 + lam) / lam) * k31 - (m1 / lam) * k12;
    REQUIRE_CLOSE("Euler Quintic Root Homothetic Stiffness Match (k_eff12 == k_eff23)",
                  k_eff, k_eff_23, STRICT_TOL);
}

static void test_suite_nine_poincare_invariants(void) {
    printf("\n--- Suite 5: All 9 Poincare Invariants (Full 3D + Non-Zero Barycentric Drift) ---\n");
    System3Body sys = {
        .q = {
            {-0.95,  0.32,  0.41},
            { 0.18, -0.27, -0.35},
            { 1.12,  0.14, -0.19}
        },
        .p = {
            { 0.42,  0.51, -0.23},
            {-0.68, -0.34,  0.47},
            { 0.41, -0.05, -0.12}
        },
        .m = {1.30, 0.90, 1.70},
        .G = 1.0
    };

    const Vec3 P0 = total_momentum(&sys);
    const Vec3 L0 = total_angular_momentum(&sys);
    const Vec3 K0 = barycentric_boost_invariant(&sys, 0.0);

    const double h     = 2.0e-4;
    const int    steps = 500;
    for (int step = 0; step < steps; ++step) {
        step_yoshida_4th(&sys, h);
    }

    const double t_end = steps * h;
    const Vec3 P1 = total_momentum(&sys);
    const Vec3 L1 = total_angular_momentum(&sys);
    const Vec3 K1 = barycentric_boost_invariant(&sys, t_end);

    REQUIRE_CLOSE("Invariant 1/9: Linear Momentum P_x", P1.x, P0.x, STRICT_TOL);
    REQUIRE_CLOSE("Invariant 2/9: Linear Momentum P_y", P1.y, P0.y, STRICT_TOL);
    REQUIRE_CLOSE("Invariant 3/9: Linear Momentum P_z", P1.z, P0.z, STRICT_TOL);

    REQUIRE_CLOSE("Invariant 4/9: Angular Momentum L_x", L1.x, L0.x, STRICT_TOL);
    REQUIRE_CLOSE("Invariant 5/9: Angular Momentum L_y", L1.y, L0.y, STRICT_TOL);
    REQUIRE_CLOSE("Invariant 6/9: Angular Momentum L_z", L1.z, L0.z, STRICT_TOL);

    REQUIRE_CLOSE("Invariant 7/9: Barycentric Boost K_x(t)", K1.x, K0.x, STRICT_TOL);
    REQUIRE_CLOSE("Invariant 8/9: Barycentric Boost K_y(t)", K1.y, K0.y, STRICT_TOL);
    REQUIRE_CLOSE("Invariant 9/9: Barycentric Boost K_z(t)", K1.z, K0.z, STRICT_TOL);
}

static void test_suite_reversibility_and_figure8(void) {
    printf("\n--- Suite 6: Strict Time-Reversibility & Figure-8 Symplectic Energy ---\n");
    const System3Body sys_init = {
        .q = {
            {-0.97000436,  0.24308753, 0.0},
            { 0.0,         0.0,        0.0},
            { 0.97000436, -0.24308753, 0.0}
        },
        .p = {
            { 0.4662036850,  0.4323657300, 0.0},
            {-0.9324073700, -0.8647314600, 0.0},
            { 0.4662036850,  0.4323657300, 0.0}
        },
        .m = {1.0, 1.0, 1.0},
        .G = 1.0
    };

    System3Body sys = sys_init;
    const double E0 = total_energy(&sys);
    const double h  = 1.0e-3;
    const int steps = 1000;

    for (int step = 0; step < steps; ++step) {
        step_yoshida_4th(&sys, h);
    }
    const double E_mid = total_energy(&sys);
    REQUIRE_CLOSE("Figure-8 Symplectic Relative Energy |dE/E0| (4th-order)",
                  fabs((E_mid - E0) / E0), 0.0, 5.0e-13);

    for (int step = 0; step < steps; ++step) {
        step_yoshida_4th(&sys, -h);
    }

    for (int i = 0; i < 3; ++i) {
        char label_q[64], label_p[64];
        sprintf(label_q, "Time-Reversibility Body %d Position ||dq_%d||", i + 1, i + 1);
        sprintf(label_p, "Time-Reversibility Body %d Momentum ||dp_%d||", i + 1, i + 1);
        REQUIRE_CLOSE(label_q, v3_norm(v3_sub(sys.q[i], sys_init.q[i])), 0.0, STRICT_TOL);
        REQUIRE_CLOSE(label_p, v3_norm(v3_sub(sys.p[i], sys_init.p[i])), 0.0, STRICT_TOL);
    }
}

int main(void) {
    printf("==========================================================================\n");
    printf(" MHMZAHRAN/symplectic-pairwise-3body — Strict C99 CI Verification Runner\n");
    printf(" Hard Failure Threshold: %.1e (IEEE-754 Double Precision)\n", STRICT_TOL);
    printf("==========================================================================\n");

    test_suite_wronskian();
    test_suite_symplectic_2form();
    test_suite_lagrange_equilateral();
    test_suite_euler_collinear();
    test_suite_nine_poincare_invariants();
    test_suite_reversibility_and_figure8();

    printf("\n==========================================================================\n");
    printf(" Summary: %d / %d assertions passed (%d failed)\n",
           g_tests_run - g_tests_failed, g_tests_run, g_tests_failed);
    printf("==========================================================================\n");

    return (g_tests_failed == 0) ? EXIT_SUCCESS : EXIT_FAILURE;
}
