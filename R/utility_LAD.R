# Common R functions of LagrangeAcademy: the one entry point from the chapters to RiemannFinMath.
#
# The roles are divided:
# - Rust (RiemannFinMath) computes prices and sensitivities. The chapters use the R package as it is
#   installed (R CMD INSTALL); nothing here builds Rust while a chapter is rendered.
# - Lean proves the identities and inequalities the calculations rest on.
# - R, in this file, prepares the inputs, calls the public functions of RiemannFinMath and shapes the
#   results into tables and figures. No function here writes a pricing formula in R.
#
# The chapters on Rust (chapter 1) and on Lean (chapters 3 to 5) also show source code as teaching
# material; the functions of section 2 read those sources as they are.
#
# The names follow LagrangeFinance's R/utility_LFL.R, with the suffix _LAD.


# ---- 1. the project and the package --------------------------------------------------------------

#' The root of the LagrangeAcademy project: the folder that holds _quarto.yml.
find_project_dir_LAD <- function() {
  candidates <- unique(c(
    Sys.getenv("QUARTO_PROJECT_DIR"),
    getwd(),
    dirname(getwd()),
    dirname(dirname(getwd()))
  ))
  candidates <- candidates[nzchar(candidates)]
  hit <- candidates[file.exists(file.path(candidates, "_quarto.yml"))]

  if (!length(hit)) {
    stop("LagrangeAcademy project root was not found.", call. = FALSE)
  }

  normalizePath(hit[1], winslash = "/", mustWork = TRUE)
}

#' The folder of the RiemannFinMath sources, next to this project (read only by section 2).
get_riemann_dir_LAD <- function() {
  normalizePath(file.path(find_project_dir_LAD(), "..", "Riemann"), winslash = "/", mustWork = FALSE)
}

#' Check that the installed R package RiemannFinMath can be loaded, and return its version.
#'
#' The chapters do not build it: install it beforehand with `R CMD INSTALL` from the RiemannFinMath
#' repository.
check_riemann_package_LAD <- function() {
  if (!requireNamespace("RiemannFinMath", quietly = TRUE)) {
    stop(
      "RiemannFinMath is not installed. Install the built package with R CMD INSTALL ",
      "(the chapters do not build Rust).",
      call. = FALSE
    )
  }

  as.character(utils::packageVersion("RiemannFinMath"))
}

#' The version and the loaded shared library of RiemannFinMath, as a one-row tibble.
get_riemann_package_info_LAD <- function() {
  version <- check_riemann_package_LAD()
  loadNamespace("RiemannFinMath")
  dll <- getLoadedDLLs()[["RiemannFinMath"]]

  tibble::tibble(
    package = "RiemannFinMath",
    version = version,
    library = if (is.null(dll)) NA_character_ else basename(dll[["path"]])
  )
}


# ---- 2. showing sources as teaching material -----------------------------------------------------

#' Print a source file (or some of its lines) as a fenced code block, for a chunk with `output: asis`.
#'
#' The file is read as it is, so that the text shown is the text that was checked or compiled.
show_source_LAD <- function(path, language, lines = NULL) {
  if (!file.exists(path)) {
    stop("The source file does not exist: ", path, call. = FALSE)
  }

  text <- readLines(path, encoding = "UTF-8", warn = FALSE)

  if (!is.null(lines)) {
    text <- text[lines]
  }

  cat(paste0("```", language), text, "```", sep = "\n")
  invisible(path)
}

#' Print a Lean file of the project's Lean library (lean/LagrangeAcademy/<name>.lean).
show_lean_source_LAD <- function(name) {
  show_source_LAD(
    file.path(find_project_dir_LAD(), "lean", "LagrangeAcademy", paste0(name, ".lean")),
    "lean"
  )
}

#' Print the statement of one Lean theorem: its doc comment and the lines up to `:= by`. The proof is
#' left out; the statement shown is the one Lean checked.
show_lean_theorem_LAD <- function(name, theorem) {
  path <- file.path(find_project_dir_LAD(), "lean", "LagrangeAcademy", paste0(name, ".lean"))

  if (!file.exists(path)) {
    stop("The Lean file does not exist: ", path, call. = FALSE)
  }

  text <- readLines(path, encoding = "UTF-8", warn = FALSE)
  start <- which(grepl(paste0("^theorem ", theorem, "( |$)"), text))[1]

  if (is.na(start)) {
    stop("The theorem ", theorem, " was not found in ", name, ".lean", call. = FALSE)
  }

  end <- which(seq_along(text) >= start & grepl(":=( by)?\\s*$", text))[1]

  # the doc comment just above the theorem, from its opening "/--"
  first <- start
  if (start > 1L && grepl("-/\\s*$", text[start - 1L])) {
    first <- max(which(grepl("^/--", text[seq_len(start - 1L)])))
  }

  show_source_LAD(path, "lean", first:end)
}

#' Print one Rust function of RiemannFinMath, with its doc comments, from its source file.
#'
#' @param file The source file under crates/riemann/src, for example "prdc.rs".
#' @param name The function's name.
show_rust_function_LAD <- function(file, name) {
  path <- file.path(get_riemann_dir_LAD(), "crates", "riemann", "src", file)

  if (!file.exists(path)) {
    stop("The RiemannFinMath source does not exist: ", path, call. = FALSE)
  }

  text <- readLines(path, encoding = "UTF-8", warn = FALSE)
  start <- which(grepl(paste0("^(pub )?fn ", name, "[<(]"), text))[1]

  if (is.na(start)) {
    stop("The function ", name, " was not found in ", file, call. = FALSE)
  }

  while (start > 1L && grepl("^///", text[start - 1L])) {
    start <- start - 1L
  }

  end <- which(seq_along(text) > start & text == "}")[1]
  show_source_LAD(path, "rust", start:end)
}

#' Print one function of this file, with its comments: the entry point that a chapter calls.
show_utility_function_LAD <- function(name) {
  path <- file.path(find_project_dir_LAD(), "R", "utility_LAD.R")
  text <- readLines(path, encoding = "UTF-8", warn = FALSE)
  start <- which(grepl(paste0("^", name, " <- function"), text))[1]

  if (is.na(start)) {
    stop("The function ", name, " was not found in utility_LAD.R", call. = FALSE)
  }

  while (start > 1L && grepl("^#'", text[start - 1L])) {
    start <- start - 1L
  }

  end <- which(seq_along(text) > start & text == "}")[1]
  show_source_LAD(path, "r", start:end)
}


# ---- 3. preparing inputs -------------------------------------------------------------------------

#' Flat continuously compounded curves of the two currencies of an FX product.
#'
#' @return A list with `domestic` and `foreign` curves of RiemannFinMath.
create_flat_curves_LAD <- function(today, domestic_rate, foreign_rate) {
  list(
    domestic = RiemannFinMath::create_flat_curve(today, domestic_rate, "actual_365_fixed", "continuous"),
    foreign = RiemannFinMath::create_flat_curve(today, foreign_rate, "actual_365_fixed", "continuous")
  )
}

#' An FX smile quoted by delta, as inputs: the spot, the expiries, the deltas and one row of
#' volatilities per expiry (puts, ATM, calls). The smile itself is made by RiemannFinMath when a note
#' is valued.
create_fx_smile_spec_LAD <- function(spot, expiries, put_deltas, call_deltas, volatilities) {
  volatilities <- as.matrix(volatilities)

  if (nrow(volatilities) != length(expiries) ||
      ncol(volatilities) != length(put_deltas) + 1L + length(call_deltas)) {
    stop("Give one row of volatilities per expiry: the puts, ATM, then the calls.", call. = FALSE)
  }

  list(spot = spot, expiries = expiries, put_deltas = put_deltas, call_deltas = call_deltas, volatilities = volatilities)
}

#' The terms of a PRDC note as one list, so that a chapter states them once. `cap = Inf` is a note
#' without a cap (the contract's "no cap", Lean's `Cap.none`; chapter 5).
create_prdc_terms_LAD <- function(
    coupon_times,
    accrual_fractions = rep(1, length(coupon_times)),
    fx_base,
    leverage,
    subtraction,
    floor = 0,
    cap = Inf,
    notional = 1,
    redemption = notional
) {
  list(
    coupon_times = as.numeric(coupon_times),
    accrual_fractions = as.numeric(accrual_fractions),
    fx_base = fx_base,
    leverage = leverage,
    subtraction = subtraction,
    floor = floor,
    cap = cap,
    notional = notional,
    redemption = redemption
  )
}

#' The example of the book: a PRDC note on an FX smile, with synthetic inputs (no market quotes).
#'
#' The introduction, chapter 2 and chapter 9 use the same example, so that its inputs are stated once.
#'
#' @param cap The cap of the coupon; `Inf` for none.
#' @return A list with `curves`, `smile` (from [create_fx_smile_spec_LAD()]) and `terms`.
create_prdc_example_LAD <- function(cap = 0.08) {
  list(
    curves = create_flat_curves_LAD("2026-11-02", domestic_rate = 0.012, foreign_rate = 0.035),
    smile = create_fx_smile_spec_LAD(
      spot = 150,
      expiries = c(1, 2, 3),
      put_deltas = c(-0.1, -0.25),
      call_deltas = c(0.25, 0.1),
      volatilities = rbind(
        c(0.150, 0.130, 0.115, 0.118, 0.135),
        c(0.156, 0.134, 0.118, 0.121, 0.140),
        c(0.161, 0.138, 0.121, 0.124, 0.146)
      )
    ),
    terms = create_prdc_terms_LAD(1:3, fx_base = 150, leverage = 0.8, subtraction = 0.78, floor = 0, cap = cap)
  )
}

#' The inputs of an example as a table, for the text.
format_prdc_example_inputs_LAD <- function(example) {
  tibble::tibble(
    item = c("国内金利（連続複利、平坦）", "外国金利（連続複利、平坦）", "スポット", "基準の FX", "レバレッジ",
             "差し引く率", "フロア", "キャップ", "クーポン", "スマイルの満期"),
    value = c("1.2%", "3.5%", format(example$smile$spot), format(example$terms$fx_base),
              format(example$terms$leverage), format(example$terms$subtraction), format(example$terms$floor),
              if (is.finite(example$terms$cap)) scales::percent(example$terms$cap) else "なし",
              sprintf("年 1 回、%d 本", length(example$terms$coupon_times)),
              paste(example$smile$expiries, collapse = "、"))
  )
}


# ---- 4. calling RiemannFinMath -------------------------------------------------------------------

#' Value a PRDC note on an FX smile with RiemannFinMath.
#'
#' RiemannFinMath makes the smile (create_fx_smile) and values the note by static replication
#' (compute_prdc_smile_value), in Rust. The values are returned as they come.
#'
#' @param curves The list of [create_flat_curves_LAD()].
#' @param smile The list of [create_fx_smile_spec_LAD()].
#' @param terms The list of [create_prdc_terms_LAD()].
#' @return The list of compute_prdc_smile_value(): `summary`, `coupons` and `pillar_vega`.
compute_prdc_smile_value_LAD <- function(curves, smile, terms) {
  check_riemann_package_LAD()
  fx_smile <- RiemannFinMath::create_fx_smile(
    smile$spot, curves$domestic, curves$foreign, smile$expiries, smile$put_deltas, smile$call_deltas,
    smile$volatilities
  )
  RiemannFinMath::compute_prdc_smile_value(
    fx_smile, terms$coupon_times, terms$accrual_fractions, terms$fx_base, terms$leverage,
    terms$subtraction, terms$floor, terms$cap, terms$notional, terms$redemption
  )
}

#' Value a PRDC note with RiemannFinMath for each spot of a grid: R makes the grid, RiemannFinMath
#' values each point (the smile's strikes move with the spot).
#'
#' @return A tibble with `spot` and the summary of each valuation.
compute_prdc_smile_values_LAD <- function(spots, curves, smile, terms) {
  purrr::map(spots, \(spot) {
    result <- compute_prdc_smile_value_LAD(curves, utils::modifyList(smile, list(spot = spot)), terms)
    tibble::add_column(result$summary, spot = spot, .before = 1)
  }) |>
    purrr::list_rbind()
}


# ---- 5. shaping results into tables and figures --------------------------------------------------

#' A table of results with rounded numbers.
show_table_LAD <- function(x, digits = 4, caption = NULL) {
  knitr::kable(x, digits = digits, caption = caption, format.args = list(big.mark = ","))
}

#' The coupons of a valuation, with the columns the text discusses. A strike that does not exist (the
#' second call of a note without a cap) comes back from RiemannFinMath as NaN.
format_prdc_coupons_LAD <- function(result) {
  result$coupons[, c("time", "forward", "floor_strike", "floor_volatility", "cap_strike", "cap_volatility", "rate", "value")]
}

#' The summaries of several valuations side by side: one row per named result.
#'
#' @param results A named list of results of [compute_prdc_smile_value_LAD()].
format_prdc_summaries_LAD <- function(results) {
  purrr::imap(results, \(result, name) tibble::add_column(result$summary, note = name, .before = 1)) |>
    purrr::list_rbind()
}

#' The ggplot2 theme of LagrangeAcademy.
create_academy_theme_LAD <- function(base_size = 12) {
  ggplot2::theme_minimal(base_size = base_size) +
    ggplot2::theme(
      panel.grid.minor = ggplot2::element_blank(),
      plot.title = ggplot2::element_text(face = "bold")
    )
}

#' Plot the coupons of a valuation: each coupon's expected rate by its time.
plot_prdc_coupons_LAD <- function(result) {
  coupons <- result$coupons
  ggplot2::ggplot(coupons, ggplot2::aes(time, rate)) +
    ggplot2::geom_col(width = 0.4) +
    ggplot2::scale_y_continuous(labels = scales::label_percent(accuracy = 0.01)) +
    ggplot2::labs(
      x = "クーポンの時点（年）",
      y = "期待クーポン",
      caption = sprintf(
        "フロアの FX 水準 %.2f、キャップの FX 水準 %s（RiemannFinMath が計算）",
        coupons$floor_strike[1],
        if (is.nan(coupons$cap_strike[1])) "なし" else sprintf("%.2f", coupons$cap_strike[1])
      )
    ) +
    create_academy_theme_LAD()
}

#' Plot the value against the spot, from [compute_prdc_smile_values_LAD()].
plot_prdc_value_by_spot_LAD <- function(values) {
  ggplot2::ggplot(values, ggplot2::aes(spot, value)) +
    ggplot2::geom_line() +
    ggplot2::geom_point() +
    ggplot2::labs(x = "FX スポット", y = "ノートの価格（名目 1）") +
    create_academy_theme_LAD()
}


# the chapters need the installed package; fail where a chapter starts, with the reason
check_riemann_package_LAD()
