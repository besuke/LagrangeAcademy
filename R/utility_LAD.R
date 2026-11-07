# Common R functions of LagrangeAcademy.
#
# The roles are divided: Rust (RiemannFinMath) computes, Lean proves, and R only shapes the inputs and
# shows the results. No function here computes a price; prices come from RiemannFinMath.
# The names follow LagrangeFinance's R/utility_LFL.R, with the suffix _LAD.


# ---- the project ---------------------------------------------------------------------------------

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

#' The folder of the RiemannFinMath sources, next to this project.
get_riemann_dir_LAD <- function() {
  normalizePath(file.path(find_project_dir_LAD(), "..", "Riemann"), winslash = "/", mustWork = FALSE)
}


# ---- showing sources -----------------------------------------------------------------------------

#' Print a source file as a fenced code block, for a chunk with `output: asis`.
#'
#' The file is read as it is, so that the text shown is the text that was checked or compiled.
#'
#' @param path The file.
#' @param language The language of the fence ("lean", "rust", "r").
#' @param lines Optional line numbers to show.
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

#' Print one Rust function of RiemannFinMath, from its `fn` line to the line that closes it.
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

  # the doc comments just above the function
  while (start > 1L && grepl("^///", text[start - 1L])) {
    start <- start - 1L
  }

  end <- which(seq_along(text) > start & text == "}")[1]
  show_source_LAD(path, "rust", start:end)
}


# ---- inputs for RiemannFinMath -------------------------------------------------------------------

#' Flat continuously compounded curves of the two currencies of an FX product.
#'
#' @param today The reference date.
#' @param domestic_rate,foreign_rate Continuous rates.
#'
#' @return A list with `domestic` and `foreign` curves of RiemannFinMath.
create_flat_curves_LAD <- function(today, domestic_rate, foreign_rate) {
  list(
    domestic = RiemannFinMath::create_flat_curve(today, domestic_rate, "actual_365_fixed", "continuous"),
    foreign = RiemannFinMath::create_flat_curve(today, foreign_rate, "actual_365_fixed", "continuous")
  )
}

#' The terms of a PRDC note as one list, so that a chapter states them once.
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

#' Value a PRDC note on an FX smile with RiemannFinMath for each spot of a grid.
#'
#' R only builds a smile per spot (the inputs); the valuation is RiemannFinMath's
#' compute_prdc_smile_value() in Rust.
#'
#' @param spots FX spots.
#' @param curves The list of [create_flat_curves_LAD()].
#' @param expiries,put_deltas,call_deltas,volatilities The smile, as create_fx_smile().
#' @param terms The list of [create_prdc_terms_LAD()].
#'
#' @return A tibble with `spot` and the summary of each valuation.
compute_prdc_smile_values_LAD <- function(spots, curves, expiries, put_deltas, call_deltas, volatilities, terms) {
  purrr::map(spots, \(spot) {
    smile <- RiemannFinMath::create_fx_smile(
      spot, curves$domestic, curves$foreign, expiries, put_deltas, call_deltas, volatilities
    )
    result <- RiemannFinMath::compute_prdc_smile_value(
      smile, terms$coupon_times, terms$accrual_fractions, terms$fx_base, terms$leverage,
      terms$subtraction, terms$floor, terms$cap, terms$notional, terms$redemption
    )
    tibble::add_column(result$summary, spot = spot, .before = 1)
  }) |>
    purrr::list_rbind()
}


# ---- showing results -----------------------------------------------------------------------------

#' A table of results with rounded numbers.
#'
#' @param x A data frame.
#' @param digits Digits after the decimal point.
#' @param caption The caption.
show_table_LAD <- function(x, digits = 4, caption = NULL) {
  knitr::kable(x, digits = digits, caption = caption, format.args = list(big.mark = ","))
}

#' The ggplot2 theme of LagrangeAcademy.
create_academy_theme_LAD <- function(base_size = 12) {
  ggplot2::theme_minimal(base_size = base_size) +
    ggplot2::theme(
      panel.grid.minor = ggplot2::element_blank(),
      plot.title = ggplot2::element_text(face = "bold")
    )
}

#' Plot the coupons of a PRDC valuation: each coupon's expected rate by its time, with the FX levels
#' of its floor and cap in the caption.
#'
#' @param coupons The `coupons` tibble of compute_prdc_smile_value().
plot_prdc_coupons_LAD <- function(coupons) {
  ggplot2::ggplot(coupons, ggplot2::aes(time, rate)) +
    ggplot2::geom_col(width = 0.4) +
    ggplot2::scale_y_continuous(labels = scales::label_percent(accuracy = 0.01)) +
    ggplot2::labs(
      x = "クーポンの時点（年）",
      y = "期待クーポン",
      caption = sprintf(
        "フロアの FX 水準 %.2f、キャップの FX 水準 %.2f（RiemannFinMath が計算）",
        coupons$floor_strike[1], coupons$cap_strike[1]
      )
    ) +
    create_academy_theme_LAD()
}

#' Plot a value and its deltas against the spot, from [compute_prdc_smile_values_LAD()].
plot_prdc_value_by_spot_LAD <- function(values) {
  ggplot2::ggplot(values, ggplot2::aes(spot, value)) +
    ggplot2::geom_line() +
    ggplot2::geom_point() +
    ggplot2::labs(x = "FX スポット", y = "ノートの価格（名目 1）") +
    create_academy_theme_LAD()
}
