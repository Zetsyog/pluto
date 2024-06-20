#include <stdio.h>
#include <stdlib.h>

#include "cloog/cloog.h"
#include "math_support.h"
#include "pluto.h"
#include "pluto/matrix.h"
#include "trahrhe.h"
#include "trahrhe_codegen.h"

void insert_tiling_statements(struct clast_stmt *root, const PlutoProg *prog,
                              CloogOptions *cloogOptions, FILE *outfp);

static int get_stmt_trans_row_number(Stmt *stmt, int tiled_loop_dim) {
  for (int i = 0; i < stmt->trans->nrows; i++) {
    if (pluto_matrix_rows_are_equal(
            stmt->trans, i, stmt->tiled_depth_to_trans_mat_row[tiled_loop_dim],
            0)) {
      return i;
    }
  }
  return -1;
}

/*
  Return a pointer to next statement according to the depth first traversal of
  the syntax tree
*/
struct clast_stmt **clast_get_next_ptr(struct clast_stmt *stmt) {
  if (CLAST_STMT_IS_A(stmt, stmt_for)) {
    return &((struct clast_for *)stmt)->body;
  } else if (CLAST_STMT_IS_A(stmt, stmt_guard)) {
    return &((struct clast_guard *)stmt)->then;
  } else if (CLAST_STMT_IS_A(stmt, stmt_block)) {
    return &((struct clast_block *)stmt)->body;
  } else {
    return &stmt->next;
  }
}

int trahrhe_clast_pass_remove_outermost_guards(CloogOptions *options,
                                               struct clast_stmt *root) {
  fprintf(stderr, "[trahrhe-ast] remove guards pass\n");
  if (root == NULL && root->next == NULL)
    return 0;

  struct clast_stmt *prev = root;
  struct clast_stmt *stmt = root->next;
  int removed = 0;
  // Iterate through statement
  while (stmt != NULL) {
    // If the statement is a guard
    if (CLAST_STMT_IS_A(stmt, stmt_guard)) {
      struct clast_guard *guard = (struct clast_guard *)stmt;
      struct clast_stmt *content = guard->then;

      prev->next = content;
      for (; content->next != NULL; content = content->next)
        ;
      content->next = stmt->next;

      stmt = content;

      guard->then = NULL;
      guard->stmt.next = NULL;
      cloog_clast_free((struct clast_stmt *)guard);

      removed++;
    }
    prev = stmt;
    stmt = stmt->next;
  }
  return removed;
}

/*
  Return the next statement according to the depth first traversal of the
    syntax tree
*/
struct clast_stmt *clast_get_next(struct clast_stmt *stmt) {
  return *clast_get_next_ptr(stmt);
}

int clast_stmt_is_branch(struct clast_stmt *stmt) {
  return CLAST_STMT_IS_A(stmt, stmt_for) || CLAST_STMT_IS_A(stmt, stmt_guard) ||
         CLAST_STMT_IS_A(stmt, stmt_block);
}

struct clast_stmt *get_stmt_before(struct clast_stmt *root,
                                   struct clast_stmt *stmt) {
  for (; root; root = root->next) {
    struct clast_stmt *syntax_next = clast_get_next(root);
    if (root->next == stmt || syntax_next == stmt) {
      return root;
    }
    if (clast_stmt_is_branch(stmt)) {
      struct clast_stmt *before = get_stmt_before(syntax_next, stmt);
      if (before != NULL) {
        return before;
      }
    }
  }
  return NULL;
}

/*
  Set the next statement according to the depth first traversal of the
    syntax tree
*/
void clast_set_next(struct clast_stmt *stmt, struct clast_stmt *next) {
  *clast_get_next_ptr(stmt) = next;
}

/*
  Insert a statement after another following the depth first traversal of the
    syntax tree
  Returns inserted statement for multiple insertion convenience
*/
struct clast_stmt *clast_insert_after(struct clast_stmt *before,
                                      struct clast_stmt *stmt) {
  stmt->next = clast_get_next(before);
  clast_set_next(before, stmt);
  return stmt;
}

void replace_tiled_loop_bounds(struct clast_stmt *root, const PlutoProg *prog,
                               CloogOptions *cloogOptions) {
  assert(root != NULL);

  Band **bands;
  unsigned nbands;
  bands = pluto_get_outermost_permutable_bands((PlutoProg *)prog, &nbands);

  for (unsigned j = 0; j < nbands; j++) {
    Band *band = bands[j];
    Ploop *loop = band->loop;
    pluto_loop_print(loop);

    int *stmtids = (int *)malloc(loop->nstmts * sizeof(int));
    int max_tiled_loops = 0;
    Stmt *tiled_stmt = loop->stmts[0];
    for (unsigned j = 0; j < loop->nstmts; j++) {
      Stmt *stmt = loop->stmts[j];
      stmtids[j] = stmt->id + 1;
      if (stmt->tiled_loops > max_tiled_loops) {
        max_tiled_loops = stmt->tiled_loops;
        tiled_stmt = stmt;
      }
    }

    for (int i = 0; i < max_tiled_loops; i++) {
      fprintf(stderr, "[trahrhe-ast] Tiling loop %d\n", i);
      unsigned nloops, nstmts;
      int *stmts;
      struct clast_for **loops;
      char iter[13];

      pluto_matrix_print(stderr, tiled_stmt->tiled_depth_to_trans_mat_row[i]);
      fprintf(stderr, "\n");

      int iter_idx = get_stmt_trans_row_number(tiled_stmt, i);

      sprintf(iter, "t%d", iter_idx + 1);

      ClastFilter filter = {iter, stmtids, (int)loop->nstmts, subset};
      clast_filter(root, filter, &loops, (int *)&nloops, &stmts,
                   (int *)&nstmts);

      fprintf(stderr, "[trahrhe-ast] Looking for iter: %s\n", iter);
      for (unsigned j = 0; j < nloops; j++) {
        // create clast_name for lower and upper bounds
        struct clast_name *clast_atiling_lb = new_clast_name(
            ((struct clast_root *)root)
                ->names->parameters[tiled_stmt->tiled_params_idx[i] + 0]);

        struct clast_name *clast_atiling_ub = new_clast_name(
            ((struct clast_root *)root)
                ->names->parameters[tiled_stmt->tiled_params_idx[i] + 1]);

        // add parametric dep for lower bound
        struct clast_reduction *clast_lb =
            new_clast_reduction(clast_red_max, 2);
        clast_lb->elts[0] = (struct clast_expr *)clast_atiling_lb;
        clast_lb->elts[1] = loops[j]->LB;

        loops[j]->LB = (struct clast_expr *)clast_lb;

        struct clast_reduction *clast_ub =
            new_clast_reduction(clast_red_min, 2);
        clast_ub->elts[0] = (struct clast_expr *)clast_atiling_ub;
        clast_ub->elts[1] = loops[j]->UB;

        loops[j]->UB = (struct clast_expr *)clast_ub;
      }

      free(loops);
      free(stmts);
    }

    free(stmtids);
  }

  pluto_bands_free(bands, nbands);
}

static CloogStatement *clast_stmts = NULL;
static CloogStatement *clast_stmts_head = NULL;

static int nextStatementNumber = 0;

struct clast_user_stmt *trahrhe_clast_create_stmt(CloogOptions *cloogOptions,
                                                  CloogDomain *domain,
                                                  unsigned int *number) {
  CloogStatement *atiling_stmt =
      cloog_statement_alloc(cloogOptions->state, nextStatementNumber++);
  cloog_statement_add(&clast_stmts, &clast_stmts_head, atiling_stmt);
  *number = atiling_stmt->number;
  // struct clast_name* name new_clast_name(name);
  // struct clast_assignment* test = new_clast_assignment(NULL, name);
  struct clast_user_stmt *user_stmt =
      new_clast_user_stmt(domain, atiling_stmt, NULL);
  return user_stmt;
}

void clast_set_custom_omp_parallel(struct clast_for *loop,
                                   struct trahrhe_codegen_data *data,
                                   Stmt *stmt) {
  if (!(loop->parallel & CLAST_PARALLEL_OMP))
    return;

  loop->parallel |= CLAST_PARALLEL_USER;
  char *user_directive = malloc(512);
  strcpy(user_directive, "omp parallel for firstprivate(");

  for (int i = 0; i <= data->depth; i++) {
    if (i != 0) {
      sprintf(user_directive + strlen(user_directive), ",");
    }
    sprintf(user_directive + strlen(user_directive), "b%d_ubt%d,",
            data->band_id, i);
    sprintf(user_directive + strlen(user_directive), "b%u_t%d_pcmax,",
            data->band_id, i);
    sprintf(user_directive + strlen(user_directive), "b%u_TILE_VOL_L%d",
            data->band_id, i);
  }

  sprintf(user_directive + strlen(user_directive), ")");
  loop->user_directive = strdup(user_directive);
  free(user_directive);

  char *private_vars = malloc(512);
  strcpy(private_vars, loop->private_vars);
  sprintf(private_vars + strlen(private_vars), ",b%d_lb%d,b%d_ub%d",
          data->band_id, data->depth, data->band_id, data->depth);
  for (int i = data->depth + 1; i < stmt->num_tiled_loops; i++) {
    sprintf(private_vars + strlen(private_vars), ",b%d_ubt%d", data->band_id,
            i);
    sprintf(private_vars + strlen(private_vars),
            ",b%u_t%d_pcmax,b%u_TILE_VOL_L%d", data->band_id, i, data->band_id,
            i);

    sprintf(private_vars + strlen(private_vars), ",b%d_lb%d,b%d_ub%d",
            data->band_id, i, data->band_id, i);
  }
  free(loop->private_vars);
  loop->private_vars = strdup(private_vars);
  free(private_vars);
}

void insert_tiling_statements(struct clast_stmt *root, const PlutoProg *prog,
                              CloogOptions *cloogOptions, FILE *outfp) {
  assert(root != NULL);

  Band **bands;
  unsigned nbands;

  nextStatementNumber = prog->nstmts + 1;

  bands = pluto_get_outermost_permutable_bands((PlutoProg *)prog, &nbands);

  for (unsigned j = 0; j < nbands; j++) {
    Band *band = bands[j];
    Ploop *loop = band->loop;
    pluto_loop_print(loop);

    int *stmtids = (int *)malloc(loop->nstmts * sizeof(int));
    int max_tiled_loops = 0;
    Stmt *tiled_stmt = loop->stmts[0];
    for (unsigned j = 0; j < loop->nstmts; j++) {
      Stmt *stmt = loop->stmts[j];
      stmtids[j] = stmt->id + 1;
      if (stmt->tiled_loops > max_tiled_loops) {
        max_tiled_loops = stmt->tiled_loops;
        tiled_stmt = stmt;
      }
    }

    char *band_domain_str = pluto_band_isl_domain(band);

    for (int i = 0; i < max_tiled_loops; i++) {
      unsigned nloops, nstmts;
      int *stmts;
      struct clast_for **loops;
      char iter[13];
      sprintf(iter, "t%d", tiled_stmt->tiling_loop_depths[i] + 1);

      ClastFilter filter = {iter, stmtids, (int)loop->nstmts, subset};
      clast_filter(root, filter, &loops, (int *)&nloops, &stmts,
                   (int *)&nstmts);

      fprintf(stderr, "[trahrhe-ast] Looking for iter: %s\n", iter);
      for (unsigned k = 0; k < nloops; k++) {
        // retrieve the statement before the current loop in the ast
        struct clast_stmt *stmt_before =
            get_stmt_before(root, (struct clast_stmt *)loops[k]);

        // retrive the type of parametric tiling we must do at this depth
        enum ptile_type tiling_type = trahrhe_get_tiling_type_for_depth(
            prog, tiled_stmt->tiling_loop_depths[i]);

        // create a new ast-node for the header statement
        unsigned stmt_ids[2] = {0};
        struct clast_user_stmt *trahrhe_header_stmt = trahrhe_clast_create_stmt(
            cloogOptions, loops[k]->domain, &stmt_ids[0]);
        // insert the node before the current loop
        clast_insert_after(stmt_before,
                           (struct clast_stmt *)trahrhe_header_stmt);

        // do the same for body statement (which is inside the loop)
        struct clast_user_stmt *trahrhe_body_stmt = trahrhe_clast_create_stmt(
            cloogOptions, loops[k]->domain, &stmt_ids[1]);
        // insert the node inside the current loop
        clast_insert_after((struct clast_stmt *)loops[k],
                           (struct clast_stmt *)trahrhe_body_stmt);

        char lb_prefix[13] = {0};
        char ub_prefix[13] = {0};
        snprintf(lb_prefix, 13, "b%d_lb", j);
        snprintf(ub_prefix, 13, "b%d_ub", j);
        char *lb_expr, *ub_expr;
        get_ub_expr_from_isl(prog, band_domain_str, i, lb_prefix, ub_prefix,
                             &lb_expr, &ub_expr);

        for (int l = 0; l < 2; l++) {
          // create data structure required for code generation
          struct trahrhe_codegen_data codegen_data = {
              .stmt_type = l,
              .tiling_type = tiling_type,
              .band_id = j,
              .stmt_id = stmt_ids[l],
              .depth = i,
              .lb_expr = strdup(lb_expr),
              .ub_expr = strdup(ub_expr),
              .iterator_name = strdup(loops[k]->iterator),
          };

          // store data structure, code generation will be done later
          trahrhe_add_stmt_to_gen(prog->trahrhe_data, &codegen_data);
          if (l == 0) {
            clast_set_custom_omp_parallel(loops[k], &codegen_data, tiled_stmt);
          }
        }
        free(lb_expr);
        free(ub_expr);

        fprintf(stderr, "[trahrhe-ast] Tiling stmt: %s\n", band_domain_str);
      }
      free(loops);
      free(stmts);
    }
    free(band_domain_str);
    free(stmtids);
  }

  pluto_bands_free(bands, nbands);
}

void trahrhe_tiling_transform(struct clast_stmt *root, const PlutoProg *prog,
                              CloogOptions *cloogOptions, FILE *outfp) {
  insert_tiling_statements(root, prog, cloogOptions, outfp);
  replace_tiled_loop_bounds(root, prog, cloogOptions);

  while (trahrhe_clast_pass_remove_outermost_guards(cloogOptions, root))
    ;

  FILE *fp = fopen(TRAHRHE_GEN_FILENAME, "w");
  trahrhe_write_gen_info(prog, fp);
  fclose(fp);
}

void trahrhe_gen_stmts_macro(const PlutoProg *prog, FILE *outfp) {
  // generate statements
  for (int i = 0; i < prog->trahrhe_data->num_stmt_to_gen; i++) {
    fprintf(outfp, "#define S%d()\t",
            prog->trahrhe_data->stmt_to_gen[i].stmt_id);
    trahrhe_codegen_stmt(outfp, prog, &prog->trahrhe_data->stmt_to_gen[i]);
    fprintf(outfp, "\n");
  }
}

void trahrhe_gen_var_decls(const PlutoProg *prog, FILE *outfp) {
  for (int i = 0; i < prog->trahrhe_data->num_header_to_gen; i++) {
    fprintf(outfp, "#include \"%s\"\n",
            prog->trahrhe_data->headers_to_gen[i].filename);
  }

  // generate variable for newly created parameters
  fprintf(outfp, "long int ");
  for (int i = prog->npar_orig; i < prog->npar; i++) {
    if (i != prog->npar_orig) {
      fprintf(outfp, ", ");
    }
    fprintf(outfp, "%s", prog->params[i]);
  }
  fprintf(outfp, ";\n");

  unsigned max_tiling_depth = 0;
  for (int i = 0; i < prog->nstmts; i++) {
    if (prog->stmts[i]->tiled_loops > max_tiling_depth) {
      max_tiling_depth = prog->stmts[i]->tiled_loops;
    }
  }
  for (int i = 0; i < prog->trahrhe_data->num_stmt_to_gen; i++) {
    struct trahrhe_codegen_data *data = &prog->trahrhe_data->stmt_to_gen[i];
    if (data->stmt_type != head) {
      continue;
    }
    fprintf(outfp, "long int b%u_t%d_pcmax, b%u_TILE_VOL_L%d;\n", data->band_id,
            data->depth, data->band_id, data->depth);
  }
}