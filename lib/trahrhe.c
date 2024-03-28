#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "constraints.h"
#include "isl_support.h"
#include "math_support.h"
#include "pluto.h"
#include "pluto/matrix.h"
#include "pluto/pluto.h"
#include "program.h"
#include "trahrhe.h"

#include "isl/aff.h"
#include "isl/ctx.h"
#include "isl/map.h"
#include "isl/printer.h"
#include "isl/set.h"
#include "isl/space.h"
#include "isl/val.h"
#include "isl/val_gmp.h"

void trahrhe_codegen_header_stmt_algebraic(FILE *fp, const PlutoProg *prog,
                                           struct trahrhe_codegen_data *data);
void trahrhe_codegen_body_stmt_algebraic(FILE *fp, const PlutoProg *prog,
                                         struct trahrhe_codegen_data *data);

void isl_compute_bounds(PlutoProg *prog, Stmt *stmt) {
  isl_ctx *ctx = isl_ctx_alloc();
  isl_printer *printer = isl_printer_to_str(ctx);

  isl_set *domain_set =
      isl_set_param_from_pluto_constraints(stmt->domain, ctx, prog->npar);

  isl_space *space = isl_space_alloc(ctx, prog->npar, stmt->dim, stmt->dim);
  isl_mat *eq = isl_mat_alloc(ctx, 0, stmt->trans->ncols + stmt->dim);
  isl_mat *ineq = isl_mat_alloc(ctx, 0, stmt->trans->ncols + stmt->dim);
  int row = 0;
  for (unsigned int i = 0; i < stmt->trans->nrows; i++) {
    if (stmt->hyp_types[i] == H_SCALAR) {
      continue;
    }
    eq = isl_mat_add_zero_rows(eq, 1);
    eq = isl_mat_set_element_si(eq, row, row, 1);
    mpz_t one;
    mpz_init(one);
    mpz_set_ui(one, 1);
    for (unsigned int j = 0; j < stmt->trans->ncols; j++) {
      mpz_t tmp;
      mpz_init(tmp);
      mpz_set_sll(tmp, -stmt->trans->val[i][j]);
      isl_val *v = isl_val_from_gmp(ctx, tmp, one);
      eq = isl_mat_set_element_val(eq, row, stmt->dim + j, v);
      mpz_clear(tmp);
    }
    mpz_clear(one);
    row++;
  }
  isl_basic_map *bmap = isl_basic_map_from_constraint_matrices(
      isl_space_copy(space), eq, ineq, isl_dim_out, isl_dim_in, isl_dim_div,
      isl_dim_param, isl_dim_cst);

  isl_set *result = isl_set_apply(domain_set, isl_map_from_basic_map(bmap));

  for (int i = 0; i < prog->npar; i++) {
    result = isl_set_set_dim_name(result, isl_dim_param, i, prog->params[i]);
  }

  for (int i = 0; i < stmt->dim; i++) {
    char name[32] = {0};
    snprintf(name, 31, "t%d", i);
    result = isl_set_set_dim_name(result, isl_dim_set, i, name);
  }

  isl_printer_flush(printer);
  isl_printer_print_set(printer, result);
  char *result_str = isl_printer_get_str(printer);
  stmt->isl_scheduled_domain_str = strdup(result_str);
  fprintf(stderr, "Result: %s\n", result_str);
  free(result_str);

  isl_set_free(result);
  isl_space_free(space);
  isl_printer_free(printer);
  isl_ctx_free(ctx);
}

/**
 * @brief append the given stmt_data to the stmt_to_gen array of the trahrhe
 * prog data struct
 * stmt_data is copied
 * @param data
 * @param stmt_data
 */
void trahrhe_add_stmt_to_gen(struct trahrhe_prog_data *data,
                             struct trahrhe_codegen_data *stmt_data) {
  if (data->num_stmt_to_gen == data->alloc_stmt_to_gen) {
    data->alloc_stmt_to_gen *= 2;
    data->stmt_to_gen =
        realloc(data->stmt_to_gen,
                data->alloc_stmt_to_gen * sizeof(struct trahrhe_codegen_data));
  }
  data->stmt_to_gen[data->num_stmt_to_gen++] = *stmt_data;
}

void trahrhe_add_header_to_gen(struct trahrhe_prog_data *data,
                               struct trahrhe_header_gen_data *header_data) {
  if (data->num_header_to_gen == data->alloc_header_to_gen) {
    data->alloc_header_to_gen *= 2;
    data->headers_to_gen = realloc(data->headers_to_gen,
                                   data->alloc_header_to_gen *
                                       sizeof(struct trahrhe_header_gen_data));
  }
  data->headers_to_gen[data->num_header_to_gen++] = *header_data;
}

struct trahrhe_prog_data *trahrhe_prog_data_alloc() {
  struct trahrhe_prog_data *data = malloc(sizeof(*data));
  data->num_tiled_bands = 0;
  data->num_stmt_to_gen = 0;
  data->alloc_stmt_to_gen = 2;
  data->stmt_to_gen =
      malloc(data->alloc_stmt_to_gen * sizeof(struct trahrhe_codegen_data));
  data->num_header_to_gen = 0;
  data->alloc_header_to_gen = 2;
  data->headers_to_gen =
      calloc(data->alloc_header_to_gen, sizeof(struct trahrhe_header_gen_data));
  return data;
}

void trahrhe_prog_data_free(struct trahrhe_prog_data *data) {
  for (int i = 0; i < data->num_stmt_to_gen; i++) {
    free(data->stmt_to_gen[i].iterator_name);
    if (data->stmt_to_gen[i].ub_expr != NULL) {
      free(data->stmt_to_gen[i].ub_expr);
    }
    if (data->stmt_to_gen[i].lb_expr != NULL) {
      free(data->stmt_to_gen[i].lb_expr);
    }
  }

  for (int i = 0; i < data->num_header_to_gen; i++) {
    if (data->headers_to_gen[i].domain != NULL) {
      free(data->headers_to_gen[i].domain);
    }
  }
  free(data->headers_to_gen);

  free(data->stmt_to_gen);
  free(data);
}

void get_lb_ub_cst(PlutoConstraints *cst, unsigned var, PlutoConstraints **lb,
                   PlutoConstraints **ub) {
  *lb = NULL;
  *ub = NULL;
  for (int i = 0; i < cst->nrows - 1; i++) {
    if (cst->val[i][var] == 1 && cst->val[i + 1][var] == -1) {
      *lb = pluto_constraints_select_row(cst, i);
      *ub = pluto_constraints_select_row(cst, i + 1);
      return;
    }
  }
}

void algebraic_precompute(PlutoProg *prog) {
  fprintf(stderr, "Algebraic precompute\n");

  // for each statement
  for (unsigned s = 0; s < prog->nstmts; s++) {
    Stmt *stmt = prog->stmts[s];
    isl_compute_bounds(prog, stmt);
  }
}

void trahrhe_write_gen_info(const PlutoProg *prog, FILE *fp) {
  fprintf(stderr, "Writing trahrhe gen info\n");
  fprintf(fp, "%d\n", prog->trahrhe_data->num_tiled_bands);
  for (int i = 0; i < prog->trahrhe_data->num_header_to_gen; i++) {
    struct trahrhe_header_gen_data *header =
        &prog->trahrhe_data->headers_to_gen[i];
    fprintf(fp, "%s\n", header->domain);
    fprintf(fp, "%d\n", header->tiling_level);
    fprintf(fp, "%c\n", header->mask);
    fprintf(fp, "%s.trahrhe.b%d.h\n", prog->context->options->out_file,
            header->band_id);
  }
}

void algebraic_tiling(PlutoProg *prog) {
  fprintf(stderr, "Algebraic tiling\n");

  Band **bands;
  unsigned nbands;
  bands = pluto_get_outermost_permutable_bands((PlutoProg *)prog, &nbands);
  for (unsigned j = 0; j < nbands; j++) {
    Band *band = bands[j];
    Ploop *loop = band->loop;

    int max_tiled_loops = 0;
    Stmt *max_depth_stmt = NULL;
    for (unsigned j = 0; j < loop->nstmts; j++) {
      Stmt *stmt = loop->stmts[j];
      if (stmt->tiled_loops > max_tiled_loops) {
        max_tiled_loops = stmt->tiled_loops;
        max_depth_stmt = stmt;
      }
    }

    if (max_tiled_loops == 0) {
      continue;
    }

    prog->trahrhe_data->num_tiled_bands++;

    struct trahrhe_header_gen_data header_data;
    header_data.band_id = j;
    header_data.tiling_level = max_tiled_loops;
    header_data.mask = 'd';
    isl_ctx *ctx = isl_ctx_alloc();
    isl_basic_set *bset = isl_basic_set_read_from_str(
        ctx, max_depth_stmt->isl_scheduled_domain_str);
    for (int i = 0; i < max_tiled_loops; i++) {
      char name[32] = {0};
      snprintf(name, 31, "b%d_t%d", j, i);
      isl_basic_set_set_dim_name(bset, isl_dim_set, i, name);
    }
    char *dom = isl_basic_set_to_str(bset);
    header_data.domain = dom;
    trahrhe_add_header_to_gen(prog->trahrhe_data, &header_data);
    isl_basic_set_free(bset);
    isl_ctx_free(ctx);

    for (unsigned s = 0; s < loop->nstmts; s++) {
      Stmt *stmt = loop->stmts[s];
      stmt->tiled_params_idx = malloc(max_tiled_loops * sizeof(int));
    }

    for (int i = 0; i < max_tiled_loops; i++) {
      for (unsigned s = 0; s < loop->nstmts; s++) {
        Stmt *stmt = loop->stmts[s];
        stmt->tiled_params_idx[i] = prog->npar;
      }
      char iter[32] = {0};
      snprintf(iter, 31, "b%d_lb%d", j, i);
      pluto_prog_add_param(prog, iter, prog->npar);

      snprintf(iter, 31, "b%d_ub%d", j, i);
      pluto_prog_add_param(prog, iter, prog->npar);

      snprintf(iter, 31, "b%d_ubt%d", j, i);
      pluto_prog_add_param(prog, iter, prog->npar);
    }
  }

  // resize matrix
  for (unsigned s = 0; s < prog->nstmts; s++) {
    Stmt *stmt = prog->stmts[s];
    for (int i = 0; i < stmt->tiled_loops; i++) {
      while (stmt->tiled_depth_to_trans_mat_row[i]->ncols <
             stmt->trans->ncols) {
        pluto_matrix_add_col(stmt->tiled_depth_to_trans_mat_row[i],
                             stmt->tiled_depth_to_trans_mat_row[i]->ncols);
      }
    }
  }

  // for each statement
  for (unsigned s = 0; s < prog->nstmts; s++) {
    Stmt *stmt = prog->stmts[s];
    for (int i = 0; i < stmt->tiled_loops; i++) {
      // lower bound
      // pluto_constraints_zero_row(stmt->domain,
      // stmt->tiled_dim_cst_idx[i][0]);
      for (int j = 0; j < stmt->domain->ncols; j++) {
        if (stmt->domain->val[stmt->tiled_dim_cst_idx[i][0]][j] == -32) {
          stmt->domain->val[stmt->tiled_dim_cst_idx[i][0]][j] = 1;
        } else {
          stmt->domain->val[stmt->tiled_dim_cst_idx[i][0]][j] = 0;
        }
      }

      // upper bound
      // pluto_constraints_zero_row(stmt->domain,
      // stmt->tiled_dim_cst_idx[i][1]);
      for (int j = 0; j < stmt->domain->ncols; j++) {
        if (stmt->domain->val[stmt->tiled_dim_cst_idx[i][1]][j] == 32) {
          stmt->domain->val[stmt->tiled_dim_cst_idx[i][1]][j] = -1;
        } else {
          stmt->domain->val[stmt->tiled_dim_cst_idx[i][1]][j] = 0;
        }
      }
      stmt->domain->val[stmt->tiled_dim_cst_idx[i][1]]
                       [stmt->dim + stmt->tiled_params_idx[i] + 2] = 1;
    }
  }

  pluto_bands_free(bands, nbands);
}

void trahrhe_codegen_header_stmt(FILE *fp, const PlutoProg *prog,
                                 struct trahrhe_codegen_data *data) {
  switch (data->tiling_type) {
  case algebraic:
    trahrhe_codegen_header_stmt_algebraic(fp, prog, data);
    break;
  default:
    fprintf(stderr, "Not implemented yet\n");
    exit(1);
  }
}

void trahrhe_codegen_body_stmt(FILE *fp, const PlutoProg *prog,
                               struct trahrhe_codegen_data *data) {
  switch (data->tiling_type) {
  case algebraic:
    trahrhe_codegen_body_stmt_algebraic(fp, prog, data);
    break;
  default:
    fprintf(stderr, "Not implemented yet\n");
    exit(1);
  }
}

void trahrhe_codegen_stmt(FILE *fp, const PlutoProg *prog,
                          struct trahrhe_codegen_data *data) {
  switch (data->stmt_type) {
  case head:
    trahrhe_codegen_header_stmt(fp, prog, data);
    break;
  case body:
    trahrhe_codegen_body_stmt(fp, prog, data);
    break;
  }
}

void trahrhe_codegen_header_stmt_algebraic(FILE *fp, const PlutoProg *prog,
                                           struct trahrhe_codegen_data *data) {
  /*    Tiling upper bound computation     aub0t = DIV0 - 1;   */
  fprintf(fp, "b%d_ubt%u = DIV%u - 1; ", data->band_id, data->depth,
          data->depth);
  fprintf(fp, "\\\n"); // new line

  fprintf(fp, "t%d_pcmax = ", data->depth);
  fprintf(fp, "b%u_t%d_Ehrhart(", data->band_id, data->depth);
  for (int i = 0; i < prog->npar_orig; i++) {
    fprintf(fp, "%s", prog->params[i]);
    if (i != prog->npar_orig - 1) {
      fprintf(fp, ", ");
    }
  }
  for (int i = 0; i < data->depth; i++) {
    fprintf(fp, ", b%d_lb%d, b%d_ub%d", data->band_id, i, data->band_id, i);
  }
  fprintf(fp, ");");
  fprintf(fp, "\\\n"); // new line
  fprintf(fp, "TILE_VOL_L%d = ", data->depth);
  fprintf(fp, "t%d_pcmax / DIV%u ", data->depth, data->depth);
}

void get_ub_expr_from_isl(const PlutoProg *prog, const char *isl_str, int pos,
                          char *lb_prefix, char *ub_prefix, char **lb_expr,
                          char **ub_expr) {
  isl_ctx *ctx = isl_ctx_alloc();

  isl_basic_set *bset = isl_basic_set_read_from_str(ctx, isl_str);
  isl_size ndim = isl_basic_set_n_dim(bset);

  isl_mat *mat = isl_basic_set_inequalities_matrix(
      bset, isl_dim_set, isl_dim_div, isl_dim_param, isl_dim_cst);

  PlutoMatrix *pmat = pluto_matrix_from_isl_mat(mat, prog->context);
  pluto_matrix_add_col(pmat, 0);
  for (int i = 0; i < pmat->nrows; i++) {
    pmat->val[i][0] = 1;
  }

  PlutoConstraints *cst = pluto_constraints_from_matrix(pmat);

  pluto_matrix_free(pmat);

  PlutoConstraints *lb, *ub;
  get_lb_ub_cst(cst, pos, &lb, &ub);

  char **names = malloc(sizeof(char *) * (ndim + prog->npar_orig));
  for (int i = 0; i < ndim + prog->npar_orig; i++) {
    if (i < ndim) {
      names[i] = malloc(32 * sizeof(char));
      snprintf(names[i], 31, "%s%d", lb_prefix, i);
    } else {
      names[i] = strdup(prog->params[i - ndim]);
    }
  }

  pluto_constraints_set_names(lb, names);

  for (int i = 0; i < ndim; i++) {
    snprintf(names[i], 31, "%s%d", ub_prefix, i);
  }
  pluto_constraints_set_names(ub, names);

  pluto_constraints_pretty_print(stderr, ub);

  *lb_expr = malloc(sizeof(char) * 1024);
  *ub_expr = malloc(sizeof(char) * 1024);
  memset(*lb_expr, 0, 1024);
  memset(*ub_expr, 0, 1024);

  for (int i = 0; i < ub->ncols; i++) {
    if (i == pos) {
      continue;
    }
    if (ub->val[0][i] != 0) {
      if (i == ub->ncols - 1) {
        snprintf(*ub_expr + strlen(*ub_expr), 1023 - strlen(*ub_expr), "%c%ld",
                 ub->val[0][i] > 0 ? '+' : ' ', ub->val[0][i]);

      } else {
        snprintf(*ub_expr + strlen(*ub_expr), 1023 - strlen(*ub_expr),
                 "%c %ld*%s ", ub->val[0][i] > 0 ? '+' : ' ', ub->val[0][i],
                 ub->names[i]);
      }
    }
    if (lb->val[0][i] != 0) {
      if (i == lb->ncols - 1) {
        snprintf(*lb_expr + strlen(*lb_expr), 1023 - strlen(*lb_expr), "%c%ld",
                 lb->val[0][i] > 0 ? '+' : ' ', lb->val[0][i]);
      } else {
        snprintf(*lb_expr + strlen(*lb_expr), 1023 - strlen(*lb_expr),
                 "%c %ld*%s ", lb->val[0][i] > 0 ? '+' : ' ', lb->val[0][i],
                 lb->names[i]);
      }
    }
  }

  // free names
  for (int i = 0; i < ndim + prog->npar_orig; i++) {
    free(names[i]);
  }
  free(names);

  pluto_constraints_free(cst);
  pluto_constraints_free(lb);
  pluto_constraints_free(ub);
  isl_mat_free(mat);
  isl_basic_set_free(bset);
  isl_ctx_free(ctx);
}

void trahrhe_codegen_body_stmt_algebraic(FILE *fp, const PlutoProg *prog,
                                         struct trahrhe_codegen_data *data) {
  /*    Tiling upper bound computation     aub0t = DIV0 - 1;   */
  fprintf(fp, "b%d_lb%u = ", data->band_id, data->depth);
  fprintf(fp, "b%d_t%d_trahrhe_b%d_t%d(", data->band_id, data->depth,
          data->band_id, data->depth);
  fprintf(fp, "max(1, %s * TILE_VOL_L%d)", data->iterator_name, data->depth);

  // minimum args are prog parameters
  for (int i = 0; i < prog->npar_orig; i++) {
    fprintf(fp, ", %s", prog->params[i]);
  }
  // append bounds of previous loops
  for (int i = 0; i < data->depth; i++) {
    fprintf(fp, ", b%d_lb%u, b%d_ub%u", data->band_id, i, data->band_id, i);
  }

  fprintf(fp, ");");
  fprintf(fp, "\\\n"); // new line

  // upper bound
  fprintf(fp, "b%d_ub%u = ", data->band_id, data->depth);
  fprintf(fp, "b%d_t%d_trahrhe_b%d_t%d(", data->band_id, data->depth,
          data->band_id, data->depth);
  fprintf(fp, "min(t%d_pcmax, (%s + 1) * TILE_VOL_L%d)", data->depth,
          data->iterator_name, data->depth);
  // minimum args are prog parameters
  for (int i = 0; i < prog->npar_orig; i++) {
    fprintf(fp, ", %s", prog->params[i]);
  }
  // append bounds of previous loops
  for (int i = 0; i < data->depth; i++) {
    fprintf(fp, ", b%u_lb%d, b%u_ub%d", data->band_id, i, data->band_id, i);
  }
  fprintf(fp, ") - 1;");
  fprintf(fp, "\\\n"); // new line
  // last bound adjustment
  fprintf(fp, "if(%s == DIV%u - 1) {\\\n", data->iterator_name, data->depth);

  fprintf(fp, "b%u_ub%u = %s", data->band_id, data->depth, data->ub_expr);
  fprintf(fp, ";\\\n"); // new line

  fprintf(fp, "}");
}