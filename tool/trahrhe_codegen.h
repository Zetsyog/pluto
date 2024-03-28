#ifndef ALGEBRAIC_CODEGEN_H
#define ALGEBRAIC_CODEGEN_H

#include <stdio.h>

#include "cloog/cloog.h"

typedef struct plutoProg PlutoProg;

/**
 * Clast-based loop bounds replacement
 */
void replace_tiled_loop_bounds(struct clast_stmt *root, const PlutoProg *prog,
                               CloogOptions *cloogOptions);

void trahrhe_tiling_transform(struct clast_stmt *root, const PlutoProg *prog,
                              CloogOptions *cloogOptions, FILE *outfp);

void trahrhe_gen_stmts_macro(const PlutoProg *prog, FILE *outfp);

void trahrhe_gen_var_decls(const PlutoProg *prog, FILE *outfp);

int trahrhe_clast_pass_remove_outermost_guards(CloogOptions *options,
                                               struct clast_stmt *stmt);

#endif // ALGEBRAIC_CODEGEN_H