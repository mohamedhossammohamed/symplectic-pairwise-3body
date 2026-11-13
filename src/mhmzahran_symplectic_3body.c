/*
 * src/mhmzahran_symplectic_3body.c
 *
 * Reference C99 Implementation of the Formally Verified Symplectic Pairwise
 * Two-Body Integrator for the Three-Body Problem.
 *
 * Author: Mohammad Hossam Mohammed Ali Zahran (MHMZAHRAN)
 * Standard: ISO C99 (-std=c99 -Wall -Wextra -Werror -pedantic -O3 -fno-fast-math -lm)
 */

#include <stdio.h>
#include <math.h>

typedef struct {
    double x, y, z;
} Vec3;

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

static void step_pair_kepler(System3Body *sys, int i, int j, double tau) {
    const double mi = sys->m[i];
    const double mj = sys->m[j];
    const double mij = mi + mj;
    const double alpha = mi / mij;
    const double beta  = 1.0 - alpha;
    const double mu_ij = (mi * mj) / mij;

    Vec3 R_cm  = v3_add(v3_scale(alpha, sys->q[i]), v3_scale(beta, sys->q[j]));
    Vec3 P_cm  = v3_add(sys->p[i], sys->p[j]);
    Vec3 r0    = v3_sub(sys->q[i], sys->q[j]);
    Vec3 p_rel = v3_sub(v3_scale(beta, sys->p[i]), v3_scale(alpha, sys->p[j]));

    R_cm = v3_add(R_cm, v3_scale(tau / (2.0 * mij), P_cm));

    Vec3 v0 = v3_scale(1.0 / (2.0 * mu_ij), p_rel);
    const double mu_grav = 0.5 * sys->G * mij;
    const double r0_mag  = v3_norm(r0);
    const double v0_sq   = v3_dot(v0, v0);
    const double rv0     = v3_dot(r0, v0);
    const double inv_a   = (2.0 / r0_mag) - (v0_sq / mu_grav);
    const double sqrt_mu = sqrt(mu_grav);

    double chi = sqrt_mu * fabs(inv_a) * tau;
    if (chi == 0.0) {
        chi = sqrt_mu * tau / r0_mag;
    }

    double C = 0.5, S = 1.0 / 6.0;
    for (int iter = 0; iter < 35; ++iter) {
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
    const double w1 = 1.0 / (2.0 - cbrt2);
    const double w0 = -cbrt2 / (2.0 - cbrt2);
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

int main(void) {
    System3Body sys = {
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

    const double E0 = total_energy(&sys);
    const Vec3   P0 = total_momentum(&sys);
    const Vec3   L0 = total_angular_momentum(&sys);
    const Vec3   K0 = barycentric_boost_invariant(&sys, 0.0);

    const double h = 1e-3;
    const int steps = 10000;

    for (int step = 0; step < steps; ++step) {
        step_yoshida_4th(&sys, h);
    }

    const double t_final = steps * h;
    const double E1 = total_energy(&sys);
    const Vec3   P1 = total_momentum(&sys);
    const Vec3   L1 = total_angular_momentum(&sys);
    const Vec3   K1 = barycentric_boost_invariant(&sys, t_final);

    System3Body sys_rev = sys;
    for (int step = 0; step < steps; ++step) {
        step_yoshida_4th(&sys_rev, -h);
    }
    Vec3 q0_orig = {-0.97000436, 0.24308753, 0.0};
    double rev_err = v3_norm(v3_sub(sys_rev.q[0], q0_orig));

    printf("=== MHMZAHRAN Symplectic Pairwise 3-Body Verification Benchmark ===\n");
    printf("Steps Integrated         : %d (dt = %.4f, T_final = %.2f)\n", steps, h, t_final);
    printf("Relative Energy Error    : |dE / E0| = %.3e\n", fabs((E1 - E0) / E0));
    printf("Momentum Error (3 invs)  : ||dP||    = %.3e\n", v3_norm(v3_sub(P1, P0)));
    printf("Ang. Mom. Error (3 invs) : ||dL||    = %.3e\n", v3_norm(v3_sub(L1, L0)));
    printf("Boost Invariant (3 invs) : ||dK||    = %.3e\n", v3_norm(v3_sub(K1, K0)));
    printf("Time-Reversibility Error : ||dq_rev||= %.3e\n", rev_err);

    return 0;
}
