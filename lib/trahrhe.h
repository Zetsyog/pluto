#ifndef TRAHRHE_H
#define TRAHRHE_H

#include <stdio.h>

typedef struct plutoProg PlutoProg;

#include "pluto/pluto.h"

#define TRAHRHE_GEN_FILENAME ".trahrhe"

#if defined(__cplusplus)
extern "C" {
#endif

enum trahrhe_stmt_type { head, body };

struct trahrhe_codegen_data {
  enum trahrhe_stmt_type stmt_type;
  enum ptile_type tiling_type;
  int stmt_id;
  unsigned int band_id;
  unsigned int depth; /* current tiling depth */
  char *iterator_name;
  char *lb_expr;
  char *ub_expr;
};

struct trahrhe_header_gen_data {
  int band_id;
  int tiling_level;
  char *domain;
  char mask;
};

struct trahrhe_prog_data {
  int num_tiled_bands;
  int num_stmt_to_gen;
  int alloc_stmt_to_gen;
  int num_header_to_gen;
  int alloc_header_to_gen;
  struct trahrhe_codegen_data *stmt_to_gen;
  struct trahrhe_header_gen_data *headers_to_gen;
};

/* trahrhe_prog_data functions */
struct trahrhe_prog_data *trahrhe_prog_data_alloc();
void trahrhe_prog_data_free(struct trahrhe_prog_data *data);
void trahrhe_add_stmt_to_gen(struct trahrhe_prog_data *data,
                             struct trahrhe_codegen_data *stmt_data);

void trahrhe_codegen_stmt(FILE *fp, const PlutoProg *prog,
                          struct trahrhe_codegen_data *data);

void get_ub_expr_from_isl(const PlutoProg *prog, const char *isl_str, int pos,
                          char *lb_prefix, char *ub_prefix, char **lb_expr,
                          char **ub_expr);

void trahrhe_write_gen_info(const PlutoProg *prog, FILE *fp);

#if defined(__cplusplus)
}
#endif

#endif // TRAHRHE_H