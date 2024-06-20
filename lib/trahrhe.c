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
#include "isl/constraint.h"
#include "isl/ctx.h"
#include "isl/ilp.h"
#include "isl/map.h"
#include "isl/printer.h"
#include "isl/set.h"
#include "isl/space.h"
#include "isl/val.h"
#include "isl/val_gmp.h"

/* codegen functions */
void trahrhe_codegen_header_stmt_algebraic(FILE *fp, const PlutoProg *prog,
                                           struct trahrhe_codegen_data *data);
void trahrhe_codegen_body_stmt_algebraic(FILE *fp, const PlutoProg *prog,
                                         struct trahrhe_codegen_data *data);
void trahrhe_codegen_header_stmt_rectangular(FILE *fp, const PlutoProg *prog,
                                             struct trahrhe_codegen_data *data);
void trahrhe_codegen_body_stmt_rectangular(FILE *fp, const PlutoProg *prog,
                                           struct trahrhe_codegen_data *data);
void trahrhe_codegen_header_stmt_algebraic_stdln(
    FILE *fp, const PlutoProg *prog, struct trahrhe_codegen_data *data);
void trahrhe_codegen_body_stmt_algebraic_stdln(
    FILE *fp, const PlutoProg *prog, struct trahrhe_codegen_data *data);

__isl_give isl_basic_set *
isl_basic_set_minmax_union(__isl_take isl_basic_set *bset1,
                           __isl_take isl_basic_set *bset2);

void isl_apply_schedule_to_stmt_domain(PlutoProg *prog, Stmt *stmt) {
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
 * @brief Compute iteration domain for a given band
 * Basically we intersect all the domains of the statements in the band
 * We use isl to do that and we return the result as a string in the isl format
 * each statement domain should be provided in the isl format in the
 * stmt->isl_scheduled_domain_str field
 *
 * @param band
 * @return char*
 */
char *pluto_band_isl_domain(Band *band) {
  Ploop *loop = band->loop;

  fprintf(stderr, "[trahrhe-isl] Computing isl domain for band");
  pluto_band_print(band);

  int max_dim = 0;
  for (unsigned i = 0; i < loop->nstmts; i++) {
    Stmt *stmt = loop->stmts[i];
    if (stmt->dim > max_dim) {
      max_dim = stmt->dim;
    }
  }

  char *result = NULL;

  isl_ctx *ctx = isl_ctx_alloc();
  isl_basic_set *bset = NULL;

  for (unsigned i = 0; i < loop->nstmts; i++) {
    Stmt *stmt = loop->stmts[i];
    if (stmt->dim < max_dim) {
      continue;
    }

    isl_basic_set *stmt_domain =
        isl_basic_set_read_from_str(ctx, stmt->isl_scheduled_domain_str);
    char *str = isl_basic_set_to_str(stmt_domain);
    fprintf(stderr, "[trahrhe-isl] Stmt %d domain: %s\n", stmt->id, str);

    result = (result == NULL) ? strdup(str) : result;
    free(str);

    bset =
        (bset == NULL)
            ? isl_basic_set_copy(stmt_domain)
            : isl_basic_set_minmax_union(bset, isl_basic_set_copy(stmt_domain));

    isl_basic_set_free(stmt_domain);
  }

  char *str = isl_basic_set_to_str(bset);
  fprintf(stderr, "[trahrhe-isl] Minmax set: %s\n", str);

  isl_basic_set_free(bset);
  isl_ctx_free(ctx);

  fprintf(stderr, "[trahrhe-isl] Band domain: %s\n", result);
  free(result);
  return str;
}

/**
 * @brief compute isl domain to give to trahrhe software for standalone
 * algebraic tiling
 * This function is a hack
 * Trahrhe software tiles the dimensions in the order they appear in the domain
 * So we need to reorder the declaration  of the parameters to tell trahrhe in
 * what order we should tile But we can't use an isl map to do that, because it
 * will transform the domain, and that is not what we want
 *
 * @param isl_domain original isl domain. won't be modified by this function
 * @param first_dim dimension that should appear first
 * @return char * newly compyuted isl domain. Should be freed by caller
 */
char *trahrhe_stdln_algebraic_domain(char *isl_domain, int first_dim) {
  isl_ctx *ctx = isl_ctx_alloc();
  isl_basic_set *bset = isl_basic_set_read_from_str(ctx, isl_domain);

  int ndim = isl_basic_set_n_dim(bset);
  const char **names = malloc(sizeof(char *) * ndim);

  for (int i = 0; i < ndim; i++) {
    names[i] = isl_basic_set_get_dim_name(bset, isl_dim_set,
                                          i); // __isl_keep so no free
  }

  char *new_domain = isl_basic_set_to_str(bset);

  char *ptr = strstr(new_domain, names[0]);
  int written = 0;
  memcpy(ptr, names[first_dim], strlen(names[first_dim]));
  written += strlen(names[first_dim]);
  for (int i = 0; i < ndim; i++) {
    if (i == first_dim) {
      continue;
    }
    memcpy(ptr + written, ", ", 2);
    written += 2;
    memcpy(ptr + written, names[i], strlen(names[i]));
    written += strlen(names[i]);
  }

  // free memory
  free(names);

  isl_basic_set_free(bset);
  isl_ctx_free(ctx);

  return new_domain;
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
    if (data->headers_to_gen[i].filename != NULL) {
      free(data->headers_to_gen[i].filename);
    }
  }
  free(data->headers_to_gen);

  if (data->ptile_types != NULL) {
    free(data->ptile_types);
  }

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

void trahrhe_parse_ptile_type(PlutoProg *prog) {
  int len = strlen(prog->context->options->tiling_types);
  prog->trahrhe_data->nptile_types = len;
  prog->trahrhe_data->ptile_types = malloc(len * sizeof(enum ptile_type));
  for (int i = 0; i < len; i++) {
    switch (prog->context->options->tiling_types[i]) {
    case 'a':
      prog->trahrhe_data->ptile_types[i] = algebraic;
      break;
    case 'A':
      prog->trahrhe_data->ptile_types[i] = algebraic_standalone;
      break;
    case 'r':
      prog->trahrhe_data->ptile_types[i] = rectangular;
      break;
    case 'R':
      prog->trahrhe_data->ptile_types[i] = rectangular_standalone;
      break;
    default:
      fprintf(stderr, "Unknown tiling type %c\n",
              prog->context->options->tiling_types[i]);
      fprintf(stderr, "Tiling type must be one of thoses : 'a', 'A', 'r', 'C'");
      exit(1);
    }
  }
}

enum ptile_type trahrhe_get_tiling_type_for_depth(const PlutoProg *prog,
                                                  int depth) {
  if (depth >= prog->trahrhe_data->nptile_types) {
    return prog->trahrhe_data
        ->ptile_types[prog->trahrhe_data->nptile_types - 1];
  }
  return prog->trahrhe_data->ptile_types[depth];
}

void algebraic_precompute(PlutoProg *prog) {
  fprintf(stderr, "Algebraic precompute\n");

  trahrhe_parse_ptile_type(prog);

  // for each statement
  for (unsigned s = 0; s < prog->nstmts; s++) {
    Stmt *stmt = prog->stmts[s];
    isl_apply_schedule_to_stmt_domain(prog, stmt);
  }
}

void trahrhe_write_gen_info(const PlutoProg *prog, FILE *fp) {
  fprintf(stderr, "Writing trahrhe gen info\n");
  fprintf(fp, "%d\n", prog->trahrhe_data->num_header_to_gen);
  for (int i = 0; i < prog->trahrhe_data->num_header_to_gen; i++) {
    struct trahrhe_header_gen_data *header =
        &prog->trahrhe_data->headers_to_gen[i];
    fprintf(fp, "%s\n", header->domain);
    fprintf(fp, "%d\n", header->tiling_level);
    fprintf(fp, "%c\n", header->mask);
    fprintf(fp, "%s\n", header->filename);
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
    for (unsigned i = 0; i < loop->nstmts; i++) {
      Stmt *stmt = loop->stmts[i];
      if (stmt->tiled_loops > max_tiled_loops) {
        max_tiled_loops = stmt->tiled_loops;
      }
    }
    char *domain_str = pluto_band_isl_domain(band);

    if (max_tiled_loops == 0) {
      continue;
    }

    prog->trahrhe_data->num_tiled_bands++;

    int tiling_level = 0;
    for (int i = 0; i < max_tiled_loops; i++) {
      if (trahrhe_get_tiling_type_for_depth(prog, i) != algebraic) {
        break;
      }
      tiling_level++;
    }
    if (tiling_level != 0) {
      struct trahrhe_header_gen_data header_data;
      header_data.band_id = j;
      header_data.tiling_level = tiling_level;
      header_data.mask = 'd';
      isl_ctx *ctx = isl_ctx_alloc();
      isl_basic_set *bset = isl_basic_set_read_from_str(ctx, domain_str);
      for (int i = 0; i < max_tiled_loops; i++) {
        char name[32] = {0};
        snprintf(name, 31, "b%d_t%d", j, i);
        isl_basic_set_set_dim_name(bset, isl_dim_set, i, name);
      }
      char *dom = isl_basic_set_to_str(bset);
      header_data.domain = dom;
      header_data.filename = malloc(256 * sizeof(char));
      snprintf(header_data.filename, 255, "%s.trahrhe.b%d.h",
               prog->context->options->out_file, j);
      trahrhe_add_header_to_gen(prog->trahrhe_data, &header_data);
      isl_basic_set_free(bset);
      isl_ctx_free(ctx);
    }

    for (int i = 0; i < max_tiled_loops; i++) {
      if (trahrhe_get_tiling_type_for_depth(prog, i) != algebraic_standalone) {
        continue;
      }

      struct trahrhe_header_gen_data header_data;
      header_data.band_id = j;
      header_data.tiling_level = 1;
      header_data.mask = 'd';
      isl_ctx *ctx = isl_ctx_alloc();
      isl_basic_set *bset =
          isl_basic_set_read_from_str(ctx, strdup(domain_str));
      char name[32] = {0};
      for (int k = 0; k < max_tiled_loops; k++) {
        snprintf(name, 31, "b%d_t%d", j, k);
        isl_basic_set_set_dim_name(bset, isl_dim_set, k, name);
      }
      char *dom = isl_basic_set_to_str(bset);
      header_data.domain = trahrhe_stdln_algebraic_domain(dom, i);
      free(dom);
      header_data.filename = malloc(256 * sizeof(char));
      snprintf(header_data.filename, 255, "%s.trahrhe.b%d.%d.h",
               prog->context->options->out_file, j, i);
      trahrhe_add_header_to_gen(prog->trahrhe_data, &header_data);
      isl_basic_set_free(bset);
      isl_ctx_free(ctx);
    }

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

    free(domain_str);
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
  case algebraic_standalone:
    trahrhe_codegen_header_stmt_algebraic_stdln(fp, prog, data);
    break;
  case rectangular:
    trahrhe_codegen_header_stmt_rectangular(fp, prog, data);
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
  case algebraic_standalone:
    trahrhe_codegen_body_stmt_algebraic_stdln(fp, prog, data);
    break;
  case rectangular:
    trahrhe_codegen_body_stmt_rectangular(fp, prog, data);
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

void get_ub_expr_from_isl(const PlutoProg *prog, const char *isl_str, int pos,
                          char *lb_prefix, char *ub_prefix, char **lb_expr,
                          char **ub_expr) {
  isl_ctx *ctx = isl_ctx_alloc();
  // isl_set *set = NULL;
  isl_size list_len;

  isl_basic_set *bset = isl_basic_set_read_from_str(ctx, isl_str);
  isl_size ndim = isl_basic_set_n_dim(bset);

  isl_printer *printer = isl_printer_to_str(ctx);
  isl_printer_set_output_format(printer, ISL_FORMAT_C);

  // lower bound
  // replace original iterator names
  for (int i = 0; i < ndim; i++) {
    char name[32] = {0};
    snprintf(name, 31, "%s%d", lb_prefix, i);
    bset = isl_basic_set_set_dim_name(bset, isl_dim_set, i, name);
  }

  isl_constraint_list *cst_list = isl_basic_set_get_constraint_list(bset);
  list_len = isl_constraint_list_size(cst_list);
  for (isl_size i = 0; i < list_len; i++) {
    isl_constraint *cst = isl_constraint_list_get_at(cst_list, i);

    if (isl_constraint_is_lower_bound(cst, isl_dim_set, pos)) {
      cst = isl_constraint_set_coefficient_si(cst, isl_dim_set, pos, 0);
      cst = isl_constraint_negate(cst);

      isl_aff *aff = isl_constraint_get_aff(cst);
      isl_printer_print_aff(printer, aff);
      isl_aff_free(aff);

      *lb_expr = isl_printer_get_str(printer);
      fprintf(stderr, "Lower bound: %s\n", *lb_expr);
      isl_printer_flush(printer);
      isl_constraint_free(cst);
      break;
    }
    isl_constraint_free(cst);
  }
  isl_constraint_list_free(cst_list);

  // upper bound
  // replace original iterator names
  for (int i = 0; i < ndim; i++) {
    char name[32] = {0};
    snprintf(name, 31, "%s%d", ub_prefix, i);
    bset = isl_basic_set_set_dim_name(bset, isl_dim_set, i, name);
  }

  cst_list = isl_basic_set_get_constraint_list(bset);
  list_len = isl_constraint_list_size(cst_list);
  for (isl_size i = 0; i < list_len; i++) {
    isl_constraint *cst = isl_constraint_list_get_at(cst_list, i);

    if (isl_constraint_is_upper_bound(cst, isl_dim_set, pos)) {
      cst = isl_constraint_set_coefficient_si(cst, isl_dim_set, pos, 0);

      isl_aff *aff = isl_constraint_get_aff(cst);
      isl_printer_print_aff(printer, aff);
      isl_aff_free(aff);

      *ub_expr = isl_printer_get_str(printer);
      fprintf(stderr, "Upper bound: %s\n", *ub_expr);
      isl_printer_flush(printer);
      isl_constraint_free(cst);
      break;
    }
    isl_constraint_free(cst);
  }
  isl_constraint_list_free(cst_list);

  isl_basic_set_free(bset);
  isl_printer_free(printer);
  isl_ctx_free(ctx);
}

void trahrhe_codegen_header_stmt_algebraic(FILE *fp, const PlutoProg *prog,
                                           struct trahrhe_codegen_data *data) {
  /*    Tiling upper bound computation     aub0t = DIV0 - 1;   */
  fprintf(fp, "b%d_ubt%u = DIV%u - 1; ", data->band_id, data->depth,
          data->depth);
  fprintf(fp, "\\\n"); // new line

  fprintf(fp, "b%u_t%d_pcmax = ", data->band_id, data->depth);
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
  fprintf(fp, "b%u_TILE_VOL_L%d = ", data->band_id, data->depth);
  fprintf(fp, "b%u_t%d_pcmax / DIV%u ", data->band_id, data->depth,
          data->depth);
}

void trahrhe_codegen_body_stmt_algebraic(FILE *fp, const PlutoProg *prog,
                                         struct trahrhe_codegen_data *data) {
  /*    Tiling upper bound computation     aub0t = DIV0 - 1;   */
  fprintf(fp, "b%d_lb%u = ", data->band_id, data->depth);
  fprintf(fp, "b%d_t%d_trahrhe_b%d_t%d(", data->band_id, data->depth,
          data->band_id, data->depth);
  fprintf(fp, "max(1, %s * b%u_TILE_VOL_L%d)", data->iterator_name,
          data->band_id, data->depth);

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
  fprintf(fp, "min(b%u_t%d_pcmax, (%s + 1) * b%u_TILE_VOL_L%d)", data->band_id,
          data->depth, data->iterator_name, data->band_id, data->depth);
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

void trahrhe_codegen_header_stmt_rectangular(
    FILE *fp, const PlutoProg *prog, struct trahrhe_codegen_data *data) {
  fprintf(fp, "b%d_ubt%u = ceild(", data->band_id, data->depth);
  fprintf(fp, "%s", data->ub_expr);
  fprintf(fp, "- (%s - DIV%d - 1)", data->lb_expr, data->depth);
  fprintf(fp, ", DIV%u);", data->depth);
  fprintf(fp, "\\\n"); // new line
}
void trahrhe_codegen_body_stmt_rectangular(FILE *fp, const PlutoProg *prog,
                                           struct trahrhe_codegen_data *data) {
  fprintf(fp, "b%d_lb%u = ", data->band_id, data->depth);
  fprintf(fp, "DIV%u * %s", data->depth, data->iterator_name);
  fprintf(fp, " + %s - DIV%u - 1;", data->lb_expr, data->depth);
  fprintf(fp, "\\\n"); // new line

  fprintf(fp, "b%d_ub%u = ", data->band_id, data->depth);
  fprintf(fp, "DIV%u * %s", data->depth, data->iterator_name);
  fprintf(fp, " + DIV%u - 1", data->depth);
  fprintf(fp, " + %s - DIV%u - 1;", data->lb_expr, data->depth);
  fprintf(fp, "\\\n"); // new line
}

void trahrhe_codegen_header_stmt_algebraic_stdln(
    FILE *fp, const PlutoProg *prog, struct trahrhe_codegen_data *data) {
  /*    Tiling upper bound computation     aub0t = DIV0 - 1;   */
  fprintf(fp, "b%d_ubt%u = DIV%u - 1; ", data->band_id, data->depth,
          data->depth);
  fprintf(fp, "\\\n"); // new line

  fprintf(fp, "b%u_t%d_pcmax = ", data->band_id, data->depth);
  fprintf(fp, "b%u_t%d_Ehrhart(", data->band_id, data->depth);
  for (int i = 0; i < prog->npar_orig; i++) {
    fprintf(fp, "%s", prog->params[i]);
    if (i != prog->npar_orig - 1) {
      fprintf(fp, ", ");
    }
  }
  fprintf(fp, ");");
  fprintf(fp, "\\\n"); // new line
  fprintf(fp, "b%u_TILE_VOL_L%d = ", data->band_id, data->depth);
  fprintf(fp, "b%u_t%d_pcmax / DIV%u ", data->band_id, data->depth,
          data->depth);
}
void trahrhe_codegen_body_stmt_algebraic_stdln(
    FILE *fp, const PlutoProg *prog, struct trahrhe_codegen_data *data) {
  /*    Tiling upper bound computation     aub0t = DIV0 - 1;   */
  fprintf(fp, "b%d_lb%u = ", data->band_id, data->depth);
  fprintf(fp, "b%d_t%d_trahrhe_b%d_t%d(", data->band_id, data->depth,
          data->band_id, data->depth);
  fprintf(fp, "max(1, %s * b%u_TILE_VOL_L%d)", data->iterator_name,
          data->band_id, data->depth);

  // minimum args are prog parameters
  for (int i = 0; i < prog->npar_orig; i++) {
    fprintf(fp, ", %s", prog->params[i]);
  }

  fprintf(fp, ");");
  fprintf(fp, "\\\n"); // new line

  // upper bound
  fprintf(fp, "b%d_ub%u = ", data->band_id, data->depth);
  fprintf(fp, "b%d_t%d_trahrhe_b%d_t%d(", data->band_id, data->depth,
          data->band_id, data->depth);
  fprintf(fp, "min(b%u_t%d_pcmax, (%s + 1) * b%u_TILE_VOL_L%d)", data->band_id,
          data->depth, data->iterator_name, data->band_id, data->depth);
  // minimum args are prog parameters
  for (int i = 0; i < prog->npar_orig; i++) {
    fprintf(fp, ", %s", prog->params[i]);
  }
  fprintf(fp, ") - 1;");
  fprintf(fp, "\\\n"); // new line

  // last bound adjustment
  fprintf(fp, "if(%s == DIV%u - 1) {\\\n", data->iterator_name, data->depth);

  fprintf(fp, "b%u_ub%u = %s", data->band_id, data->depth, data->ub_expr);
  fprintf(fp, ";\\\n"); // new line

  fprintf(fp, "}");
}

__isl_give isl_constraint *
isl_basic_set_dim_lb_cst(__isl_keep isl_basic_set *bset, int pos) {
  // retrieve constraint list
  isl_constraint_list *cst_list = isl_basic_set_get_constraint_list(bset);
  isl_size list_len = isl_constraint_list_size(cst_list);
  isl_constraint *result = NULL;
  for (isl_size i = 0; i < list_len; i++) {
    isl_constraint *cst = isl_constraint_list_get_at(cst_list, i);
    if (isl_constraint_is_lower_bound(cst, isl_dim_set, pos)) {
      result = cst;
      break;
    }
    isl_constraint_free(cst);
  }

  isl_constraint_list_free(cst_list);

  return result;
}

__isl_give isl_constraint *
isl_basic_set_dim_ub_cst(__isl_keep isl_basic_set *bset, int pos) {
  // retrieve constraint list
  isl_constraint_list *cst_list = isl_basic_set_get_constraint_list(bset);
  isl_size list_len = isl_constraint_list_size(cst_list);
  isl_constraint *result = NULL;
  for (isl_size i = 0; i < list_len; i++) {
    isl_constraint *cst = isl_constraint_list_get_at(cst_list, i);
    if (isl_constraint_is_upper_bound(cst, isl_dim_set, pos)) {
      result = cst;
      break;
    }
    isl_constraint_free(cst);
  }

  isl_constraint_list_free(cst_list);

  return result;
}

/**
 * @brief Construct
 *
 * @param bset1
 * @param bset2
 * @return __isl_give*
 */
__isl_give isl_basic_set *
isl_basic_set_minmax_union(__isl_take isl_basic_set *bset1,
                           __isl_take isl_basic_set *bset2) {
  isl_size ndim1 = isl_basic_set_n_dim(bset1);
  isl_size ndim2 = isl_basic_set_n_dim(bset2);

  assert(ndim1 == ndim2);
  isl_basic_set *result =
      isl_basic_set_universe(isl_basic_set_get_space(bset1));

  for (isl_size i = 0; i < ndim1; i++) {
    isl_constraint *lb1 = isl_basic_set_dim_lb_cst(bset1, i);
    isl_constraint *lb2 = isl_basic_set_dim_lb_cst(bset2, i);
    isl_constraint *ub1 = isl_basic_set_dim_ub_cst(bset1, i);
    isl_constraint *ub2 = isl_basic_set_dim_ub_cst(bset2, i);

    if (lb1 == NULL && lb2 == NULL) {
      // no lower bound
      // no constraint
    } else if (lb1 == NULL) {
      // no lower bound in bset1
      // add lower bound of bset2
      result = isl_basic_set_add_constraint(result, isl_constraint_copy(lb2));
    } else if (lb2 == NULL) {
      // no lower bound in bset2
      // add lower bound of bset1
      result = isl_basic_set_add_constraint(result, isl_constraint_copy(lb1));
    } else {
      isl_pw_aff *aff1 = isl_pw_aff_from_aff(isl_constraint_get_aff(lb1));
      isl_pw_aff *aff2 = isl_pw_aff_from_aff(isl_constraint_get_aff(lb2));

      int cmp = isl_pw_aff_plain_cmp(aff1, aff2);

      isl_pw_aff_free(aff1);
      isl_pw_aff_free(aff2);

      if (cmp < 0) {
        // lb1 < lb2
        result = isl_basic_set_add_constraint(result, isl_constraint_copy(lb2));
      } else {
        result = isl_basic_set_add_constraint(result, isl_constraint_copy(lb1));
      }
    }

    if (ub1 == NULL && ub2 == NULL) {
      // no upper bound
      // no constraint
    } else if (ub1 == NULL) {
      // no upper bound in bset1
      // add upper bound of bset2
      result = isl_basic_set_add_constraint(result, isl_constraint_copy(ub2));
    } else if (ub2 == NULL) {
      // no upper bound in bset2
      // add upper bound of bset1
      result = isl_basic_set_add_constraint(result, isl_constraint_copy(ub1));
    } else {
      isl_pw_aff *aff1 = isl_pw_aff_from_aff(isl_constraint_get_aff(ub1));
      isl_pw_aff *aff2 = isl_pw_aff_from_aff(isl_constraint_get_aff(ub2));

      int cmp = isl_pw_aff_plain_cmp(aff1, aff2);

      isl_pw_aff_free(aff1);
      isl_pw_aff_free(aff2);
      if (cmp < 0) {
        // ub1 < ub2
        result = isl_basic_set_add_constraint(result, isl_constraint_copy(ub2));
      } else {
        result = isl_basic_set_add_constraint(result, isl_constraint_copy(ub1));
      }
    }

    isl_constraint_free(lb1);
    isl_constraint_free(lb2);
    isl_constraint_free(ub1);
    isl_constraint_free(ub2);
  }

  isl_basic_set_free(bset1);
  isl_basic_set_free(bset2);

  return result;
}