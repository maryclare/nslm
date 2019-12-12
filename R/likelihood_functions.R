pacf.ar <- function(pa) {
  p <- length(pa)
  if (p == 0) {
    return(0)
  } else if (p == 1) {
    return(pa)
  } else {
    yk <- pa[1]
    for (k in 2:p) {
      yk <- c(yk - pa[k]*rev(yk), pa[k])
    }
    return(yk)
  }
}

ar.pacf <- function(phi) {


  p <- length(phi)
  if (p == 0) {
    return(0)
  } else {
    y <- phi
    yk <- y
    pa <- numeric(p)
    for (k in (p + 1):2) {

      pa[k - 1] <- yk[k - 1]

      if (abs(yk[k - 1]) == 1) {
        break
      } else {
        yk <- (yk[-(k - 1)] + yk[k - 1]*rev(yk[-(k - 1)]))/(1 - yk[k - 1]^2)
      }

    }
    return(pa)
  }

}

logit <- function(x) {
  log(x/(1 - x))
}

expit <- function(x) {
  exp(x)/(1 + exp(x))
}

gamma.stirling.ratio <- function(x, y) {
  if (x < 171 & y < 171) {
    gamma(x)/gamma(y)
  } else if (x >= 171 & y >= 171) {
    exp((x - 1/2)*log(x - 1) - (x - 1) -
          ((y - 1/2)*log(y - 1) - (y - 1)))

  } else if (x < 171) {
    exp(log(gamma(x))-((log(2) + log(pi) + log(y - 1))/2 + (y - 1)*log(y - 1) - (y - 1)))
  } else if (y < 171) {
    exp((log(2) + log(pi) + log(x - 1))/2 + (x - 1)*log(x - 1) - (x - 1) - log(gamma(y)))
  }
}

adj.durbin <- function(Z, r) {
  E <- matrix(NA, nrow(Z), ncol(Z))
  v <- rep(NA, length(r))
  E[1, ] <- Z[1, ]
  beta <- 1
  lbeta.sum <- 0
  alpha <- r[2]
  v[1] <- r[2]
  for (k in 2:length(r)) {
    beta <- (1 - alpha^2)*beta
    lbeta.sum <- lbeta.sum + log(beta)
    # E[k, ] <- (Z[k, ] - apply(Z, 2, function(z) {sum(z[1:(k-1)]*v[(k-1):1])}))/sqrt(beta)
    E[k, ] <- (Z[k, ] - colSums(Z[1:(k-1), , drop = FALSE]*v[(k-1):1]))/sqrt(beta)
    if (k == length(r)) {
      break
    } else {
      alpha <- (r[k + 1] - sum(v[(k-1):1]*r[1:(k-1) + 1]))/beta
      v[k] <- alpha
      v[1:(k-1)] <- v[1:(k-1)] - alpha*v[(k-1):1]
    }
  }
  return(list("E" = E, "lbeta.sum" = lbeta.sum))
}

# for specified arguments ks
fi.cv <- function(ks, d) {

  cvs <- numeric(length(ks))
  if (d != 0) {
    for (k in unique(abs(ks))) {
      if (k == 0) {
        cvs[which(abs(ks) == k)] <- gamma(1 - 2*d)/(gamma(1 - d)^2)
      } else {
        cc <- gamma.stirling.ratio(d + k, 1 - d + k)
        cvs[which(abs(ks) == k)] <- cc*gamma(1 - 2*d)/((gamma(1 - d)*gamma(d)))
      }
    }
  } else {
    cvs[ks == 0] <- 1
  }
  return(cvs)
}

# Function that returns the autocovariance function of a FIMA process, i.e. an ARFIMA(0, d, q) process
fima.cv <- function(lag.max, d, theta) {
  cvs <- numeric(lag.max + 1)
  for (k in 0:lag.max) {
    nz <- which(theta != 0)
    q <- length(theta)
    maacf <- ARMAacf(ar = 0, ma = theta, lag.max = q)*(1 + sum(theta^2))
    which.nz <- c(-nz, 0, nz)
    maacf.nz <- maacf[abs(which.nz) + 1]
    cvs[k + 1] <- sum(maacf.nz*fi.cv(k - which.nz, d = d))
  }
  return(cvs)
}

psi <- function(l, theta = NULL) {
  if (l < 0) {l <- abs(l)}
  q <- length(theta)
  if (!is.null(theta)) {
    theta <- c(1, theta)
  } else {
    theta <- c(1)
  }
  if (l <= q) {
    sum(theta[(l + 1):length(theta)]*theta[1:(length(theta)-l)])
  } else {
    0
  }
}

chi <- function(j, inv.root = NULL, phi = NULL) {
  if (is.null(inv.root) & !is.null(phi)) {
    inv.root <- 1/polyroot(c(1, -phi))
  }
  (inv.root[j]*prod(1 - inv.root*inv.root[j])*prod(inv.root[j] - inv.root[-j]))^(-1)
}

new.eval <- function(rho) {
  floor(4/(1.0005 - abs(rho)))
}

hyperg.rec <- function(a, c, rho, prev) {
  (c - 1)*(prev - 1)/(rho*(a - 1))
}
hyperg.pre <- function(a, c, rho, succ) {
  (rho*(a - 1))*succ/(c - 1) + 1
}

# This is slower and just as accurate as hypergeo, as far as I can tell
hyperg <- function(a, c, rho, max.iter = Inf) {
  if (Im(rho) == 0) {
    rho <- Re(rho)
  }
  maxval <- 0.9999
  rho <- ifelse(abs(rho) > maxval, maxval*sign(rho), rho)
  i = 0
  ssum <- 0
  diff <- Inf
  # while (i <= max.iter) {
  while (abs(diff - ssum) > .Machine$double.eps & i <= max.iter) {
    # cat(abs(diff - ssum), "\n")
    if (i == 0) {
      new <- rho^i
    } else {
      new <- prod((a:(a + (i - 1)))/(c:(c + (i - 1))))*rho^i
    }
    diff <- ssum - new
    ssum <- ssum + new
    i <- i + 1
  }
  return(ssum)
}

C.fun <- function(d, h, rho, p, hg1 = NULL, hg2 = NULL, max.iter = Inf) {

  if (d == 0) {
    if (h > 0) {
      rho^h
    } else {
      rho^(2*p - h)
    }
  } else {
    # Should add Stirling here
    ratio <- gamma.stirling.ratio(d + h, 1 - d + h)
    grat <- (gamma(1 - 2*d)/(gamma(1 - d)*gamma(d)))
    # hg1 <- hypergeo(d + h, 1, 1 - d + h, rho)
    if (is.null(hg1)) {
      hg1 <- hyperg(d + h, 1 - d + h, rho, max.iter = max.iter)
    }
    # hg2 <- hypergeo(d - h, 1, 1 - d - h, rho)
    if (is.null(hg2)) {
      hg2 <- hyperg(d - h, 1 - d - h, rho, max.iter = max.iter)
    }

    ratio*grat*((rho^(2*p)*hg1 + hg2 - 1))

  }
}

#' @export
arfima.acv <- function(lag.max = 10, d = 0, theta = NULL,
                       phi = NULL, corr = TRUE, max.iter = Inf) {

  if (length(theta) == 1) {
    if (theta == 0) {
      theta <- NULL
    }
  }

  if (length(phi) == 1) {
    if (phi == 0) {
      phi <- NULL
    }
  }

  q <- ifelse(!is.null(theta), length(theta), 0)
  p <- ifelse(!is.null(phi), length(phi), 0)

  if (abs(d) <= 1000*2^(-.Machine$double.digits)) {
    d <- 0
  }

  if (!is.null(theta)) {
    ls <- seq(-q, q, by = 1)
    psis <- numeric(length(ls))
  } else {
    ls <- c(0)
    psis <- c(NA)
  }

  for (l in unique(abs(ls))) {
    psis[abs(ls) == l] <- psi(l = l, theta = theta)
  }


  if (!is.null(phi)) {
    inv.root <- 1/polyroot(c(1, -phi))
    max.eval <- new.eval(inv.root)
    count1 <- rep(0, p)
    count2 <- rep(0, p)
    chis <- numeric(p)
    for (j in 1:p) {
      chis[j] <- chi(j, inv.root = inv.root)
    }
    hgfs <- matrix(NA, nrow = (p + lag.max + q)*2 + 1, ncol = p)
    hs <- (-((p + lag.max + q))):(p + lag.max + q)
  }

  gam <- rep(0, 1 + lag.max)
  for (s in 0:lag.max) {
    for (l in ls) {
      if (length(ls) == 1) {
        l = 0
      }
      if (p > 0) {
        for (j in 1:p) {
          if (d != 0) {

            hv <- p + s - l
            if (is.na(hgfs[hs == hv, j])) {
              if (!is.na(hgfs[hs == (hv - 1), j]) & count1[j] <= max.eval[j]) {
                hgfs[hs == hv, j] <- hyperg.rec(a = d + hv,
                                                c = 1 - d + hv,
                                                rho = inv.root[j],
                                                prev = hgfs[hs == (hv - 1), j])
                count1[j] <- count1[j] + 1
              } else {

                hgfs[hs == hv, j] <- hyperg(d + hv, 1 - d + hv, inv.root[j])

                count1[j] <- 0
              }
            }
            if (is.na(hgfs[hs == -hv, j])) {
              if (!is.na(hgfs[hs == (- hv + 1), j]) & count2[j] <= max.eval[j]) {
                hgfs[hs == -hv, j] <- hyperg.pre(a = d - hv + 1,
                                                 c = 1 - d - hv + 1,
                                                 rho = inv.root[j],
                                                 succ = hgfs[hs == (- hv + 1), j])
                count2[j] <- count2[j] + 1
              } else {
                hgfs[hs == -hv, j] <- hyperg(d - hv, 1 - d - hv, inv.root[j])
                count2[j] <- 0
              }
            }

            hg1 <- hgfs[hs == hv, j]
            hg2 <- hgfs[hs == -hv, j]

            C.fun.val <- C.fun(d = d,
                               h = hv,
                               rho = inv.root[j], p = p,
                               hg1 = hg1, hg2 = hg2, max.iter = max.iter)
            gam[s + 1] <- gam[s + 1] + chis[j]*psis[l == ls]*C.fun.val
          } else {

            if (p + s - l > 0) {
              gam[s + 1] <- gam[s + 1] + chis[j]*psis[l == ls]*inv.root[j]^(p + s - l)
            } else {
              gam[s + 1] <- gam[s + 1] + chis[j]*psis[l == ls]*inv.root[j]^(2*p - (p + s - l))
            }
          }
        }
      } else if (d != 0) {
        gam[s + 1] <- gam[s + 1] + psis[l == ls]*(gamma(1 - 2*d)*gamma.stirling.ratio(d + s - l, 1 - d + s - l))/(gamma(d)*(gamma(1 - d)))
      } else if (d == 0) {
        gam[s + 1] <- ifelse(abs(s) <= q, psis[s == ls], 0)
      }
    }
  }
  if (!corr) {
    return(Re(gam))
  } else {
    return(list("rho" = Re(gam)/Re(gam[1]), "var" = Re(gam[1])))
  }
}

# Function that computes the log likelihood of an ARFIMA(p, d, q) proces
fima.ll <- function (z, theta = 0, dfrac = 0, Covar = NULL, phi = 0,
                     whi = FALSE, exact = TRUE, just.logl = TRUE, max.iter = Inf) {

  if (sum(abs(phi) == 1) > 0) {
    return(NA)
  } else {
    if (whi) {
      logl <- whi.ll(z = z, theta = theta, dfrac = dfrac, Covar = Covar, phi = phi,
                     just.logl = just.logl)

      if (just.logl) {
        return(logl)
      } else {
        return(list("logl" = logl$logl, "sse" = logl$sse, "beta" = logl$beta,
                    "fitted" = logl$fitted))
      }
    } else {

      n <- length(z)
      acv <- arfima.acv(lag.max = n - 1, d = dfrac, theta = theta,
                        phi = phi, corr = TRUE, max.iter = max.iter)
      r <- acv$r
      # r <- tacvfARFIMA(phi = phi, theta = -theta, dfrac = dfrac, maxlag = n - 1)
      # r <- r/r[1]

      if (is.null(Covar)) {
        Z <- matrix(z, nrow = n, ncol = 1)
      } else {
        Z <- cbind(z, Covar)
      }
      ad <- adj.durbin(Z = Z, r = r)
      if (is.null(Covar)) {
        sse <- sum(ad$E^2)
        beta <- NULL
      } else {
        ytRiCovar <- t(ad$E[, 1, drop = FALSE])%*%ad$E[, -1, drop = FALSE]
        sse <- crossprod(ad$E[, 1, drop = FALSE]) - crossprod(t(ytRiCovar),
                                                              tcrossprod(solve(crossprod(ad$E[, -1, drop = FALSE])),
                                                                         ytRiCovar))
        beta <- tcrossprod(solve(crossprod(ad$E[, -1, drop = FALSE])), ytRiCovar)
      }
      logl <- -ad$lbeta.sum/(2*n) - log(sse/n)/2

      if (just.logl) {
        return(logl)
      } else {
        if (!is.null(Covar)) {
          fitted <- Covar%*%beta
        } else {
          fitted <- rep(0, length(z))
        }
        return(list("logl" = logl, "sse" = sse/(n*acv$var), "beta" = beta,
                    "fitted" = fitted))
      }
    }
  }
}

# Function that returns Whittle approximation to ll
whi.ll <- function (z, theta = 0, dfrac = 0, Covar = NULL, phi = 0,
                    just.logl = TRUE) {

  n <- length(z)
  m <- floor((n - 1)/2)
  if (!is.null(Covar)) {
    linmod <- lm(z~Covar-1)
    z <- linmod$residuals
    fitted <- linmod$fitted
    beta <- linmod$coef
    sse <- summary(linmod)$sigma^2
  } else {
    fitted <- mean(z)
    sse <- var(z)
    z <- (z - mean(z))/sd(z)
    beta <- NULL
  }
  periodogram <- (Mod(fft(z))^2/(2*pi*n))[1:(n%/%2 + 1)]
  per <- periodogram[2:(m + 1)]

  frs <- (2*pi/n)*(1:m)

  far <- fma <- rep(1, m)
  p <- length(phi)
  q <- length(theta)
  if (!(sum(phi == 0) == p)) {

    cosar <- cos(cbind(frs)%*%rbind(1:p))
    sinar <- sin(cbind(frs)%*%rbind(1:p))
    Rar <- cosar%*%phi
    Iar <- sinar%*%phi
    far <- (1 - Rar)^2 + Iar^2

  }
  if (!(sum(theta == 0) == q)) {

    cosma <- cos(cbind(frs)%*%rbind(1:q))
    sinma <- sin(cbind(frs)%*%rbind(1:q))
    Rma <- cosma%*%(-theta)
    Ima <- sinma%*%(-theta)
    fma <- (1 - Rma)^2 + Ima^2

  }

  fsp <- (fma/far)*sqrt((1 - cos(frs))^2 + sin(frs)^2)^(-2*dfrac)

  logl <- -(sum(per/fsp)*(4*pi/n))
  logl <- -2*(1/(2*pi))*sum(log(fsp)*2*pi/m + 2*pi*per/(fsp*m))
  logl <- -sum(log(fsp) + per/fsp)
  if (just.logl) {
    return(logl)
  } else {
    if (!is.null(Covar)) {
      fitted <- linmod$fitted
    } else {
      fitted <- rep(0, length(z))
    }
    return(list("logl" = logl, "sse" = sse, "beta" = beta,
                "fitted" = fitted))
  }
}


# Function that takes a value of the fractional differencing parameter d and a time series x
# and returns the log likelihood,
#' @export
fima.ll.auto <- function(pars, y, d.max = 1.5, Covar = NULL, q = 0, p = 0,
                         whi = FALSE,
                         just.logl = TRUE,
                         tr = TRUE,
                         un = FALSE, max.iter = Inf) {

  # print(round(pars, 3))
  if (is.matrix(y)) {
    k <- ncol(y)
  } else {
    k <- 1
    y <- matrix(y, nrow = length(y), ncol = 1)
  }
  d <- pars[1]
  if (q > 0) {
    theta <- matrix(pars[1 + 1:(k*q)], nrow = q, ncol = k)
  } else {
    theta <- matrix(0, nrow = 1, ncol = k)
  }
  if (p > 0) {
    if (tr) { # I don't think this will work correctly with k > 1 as written
      if (un) {
        phi <- matrix(pacf.ar(expit(pars[1 + k*q + 1:(p*k)])*2 - 1), nrow = p, ncol = k)
      } else {
        phi <- matrix(pacf.ar(pars[1 + k*q + 1:(p*k)]), nrow = p, ncol = k)
      }

    } else {
      phi <-  matrix(pars[1 + k*q + 1:(p*k)], nrow = p, ncol = k)
    }
  } else {
    phi <- matrix(0, nrow = 1, ncol = k)
  }
  lls <- numeric(k)
  if (!just.logl) {
    if (!is.null(Covar)) {
      betas <- matrix(NA, nrow = ncol(Covar), ncol = k)
    }
    fits <- matrix(NA, nrow = nrow(y), ncol = k)
    sses <- numeric(k)
    thetas <- vector("list", length = k)
    phis <- vector("list", length = k)
  }
  for (j in 1:k) {
    if (d.max == 0.5) {
      z <- na.omit(y[, j])
      if (d < 0.5 & d >= -0.5) {
        dfr <- d
        newthe <- theta[, j]
        ll <- fima.ll(z, dfrac = dfr, theta = newthe, phi = phi[, j],
                      Covar = Covar, whi = whi, just.logl = just.logl, max.iter = max.iter)
      } else if (d < -0.5 & d >= -1.5) {
        pows <- expand.grid(c(0:length(theta[, j])), c(0, 1))
        tvals <- apply(expand.grid(c(1, theta[, j]), c(1, -1)), 1, prod)
        pows$pow <- rowSums(pows)
        newthe <- (aggregate(tvals, list("pow" = pows$pow), sum)$x)[-1]

        dfr <- d + 1
        ll <- fima.ll(z, dfrac = dfr, phi = phi[, j],
                      theta = newthe, Covar = Covar, whi = whi, just.logl = just.logl, max.iter = max.iter)
      }
    } else if (d.max == 1.5) {
      z <- na.omit(y[-1, j] - y[-nrow(y), j])
      if (!is.null(Covar)) {
        Covar <- Covar[-1, , drop = FALSE] - Covar[-nrow(Covar), , drop = FALSE]
        Covar <- Covar[, !(apply(Covar, 2, min) == 0 & apply(Covar, 2, max) == 0), drop = FALSE]
        if (ncol(Covar) == 0) {
          Covar <- NULL
        }
      }
      if (d < 1.5 & d >= 0.5) {
        dfr <- d - 1
        newthe <- theta[, j]
        ll <- fima.ll(z,
                      dfrac = dfr, Covar = Covar, theta = newthe,
                      phi = phi[, j], whi = whi, just.logl = just.logl, max.iter = max.iter)
      } else if (d < 0.5 & d >= -0.5) {

        pows <- expand.grid(c(0:length(theta[, j])), c(0, 1))
        tvals <- apply(expand.grid(c(1, theta[, j]), c(1, -1)), 1, prod)
        pows$pow <- rowSums(pows)
        newthe <- (aggregate(tvals, list("pow" = pows$pow), sum)$x)[-1]
        dfr <- d
        ll <- fima.ll(z, dfrac = dfr, theta = newthe,
                      phi = phi[, j], Covar = Covar, whi = whi,
                      just.logl = just.logl, max.iter = max.iter)
      } else if (d < -0.5 & d >= -1.5) {

        pows <- expand.grid(c(0:length(theta[, j])), c(0:2))
        tvals <- apply(expand.grid(c(1, theta[, j]), c(1, -2, 1)), 1, prod)
        pows$pow <- rowSums(pows)
        newthe <- (aggregate(tvals, list("pow" = pows$pow), sum)$x)[-1]

        dfr <- d + 1
        ll <- fima.ll(z, dfrac = dfr, theta = newthe,
                      phi = phi[, j], Covar = Covar, whi = whi,
                      just.logl = just.logl, max.iter = max.iter)
      }
    } else if (d.max == 2.5) {
      z <- y[-1, j] - y[-nrow(y), j]
      z <- na.omit(z[-1] - z[-length(z)])
      if (!is.null(Covar)) {
        Covar <- Covar[-1, , drop = FALSE] - Covar[-nrow(Covar), , drop = FALSE]
        Covar <- Covar[-1, , drop = FALSE] - Covar[-nrow(Covar), , drop = FALSE]
        Covar <- Covar[, !(apply(Covar, 2, min) == 0 & apply(Covar, 2, max) == 0), drop = FALSE]
        if (ncol(Covar) == 0) {
          Covar <- NULL
        }
      }
      if (d < 2.5 & d >= 1.5) {
        dfr <- d - 2
        newthe <- theta[, j]
        ll <- fima.ll(z,
                      dfrac = dfr, Covar = Covar,
                      phi = phi[, j], theta = newthe, whi = whi,
                      just.logl = just.logl, max.iter = max.iter)
      } else if (d < 1.5 & d >= 0.5) {

        pows <- expand.grid(c(0:length(theta[, j])), c(0, 1))
        tvals <- apply(expand.grid(c(1, theta[, j]), c(1, -1)), 1, prod)
        pows$pow <- rowSums(pows)
        newthe <- (aggregate(tvals, list("pow" = pows$pow), sum)$x)[-1]
        dfr <- d - 1
        ll <- fima.ll(z, dfrac = dfr, theta = newthe,
                      phi = phi[, j], Covar = Covar, whi = whi, just.logl = just.logl, max.iter = max.iter)
      } else if (d < 0.5 & d >= -0.5) {

        pows <- expand.grid(c(0:length(theta[, j])), c(0:2))
        tvals <- apply(expand.grid(c(1, theta[, j]), c(1, -2, 1)), 1, prod)
        pows$pow <- rowSums(pows)
        newthe <- (aggregate(tvals, list("pow" = pows$pow), sum)$x)[-1]
        dfr <- d
        ll <- fima.ll(z, dfrac = dfr, theta = newthe, phi = phi[, j],
                      Covar = Covar, whi = whi, just.logl = just.logl, max.iter = max.iter)
      } else if (d < -0.5 & d >= -1.5) {

        pows <- expand.grid(c(0:length(theta[, j])), c(0:3))
        tvals <- apply(expand.grid(c(1, theta[, j]), c(1, -3, 3, -1)), 1, prod)
        pows$pow <- rowSums(pows)
        newthe <- (aggregate(tvals, list("pow" = pows$pow), sum)$x)[-1]
        dfr <- d + 1
        ll <- fima.ll(z, dfrac = dfr, theta = newthe,
                      phi = phi[, j], Covar = Covar, whi = whi,
                      just.logl = just.logl, max.iter = max.iter)
      } else if (d < -1.5 & d >= -2.5) {

        pows <- expand.grid(c(0:length(theta[, j])), c(0:4))
        tvals <- apply(expand.grid(c(1, theta[, j]), c(1, -4, 6, -4, 1)), 1, prod)
        pows$pow <- rowSums(pows)
        newthe <- (aggregate(tvals, list("pow" = pows$pow), sum)$x)[-1]
        dfr <- d + 2
        ll <- fima.ll(z, dfrac = dfr, theta = newthe,
                      phi = phi[, j], Covar = Covar, whi = whi,
                      just.logl = just.logl, max.iter = max.iter)
      }
    }
    if (just.logl) {
      lls[j] <- ll
    } else {
      phis[[j]] <- phi[, j]
      thetas[[j]] <- newthe
      lls[j] <- ll$logl
      if (!is.null(Covar)) {
        betas[(nrow(betas) - length(ll$beta) + 1):nrow(betas), j] <- ll$beta
      }
      fits[(nrow(fits) - length(ll$fitted) + 1):nrow(fits), j] <- ll$fitted
      sses[j] <- ll$sse
    }
  }
  if (just.logl) {
    return(sum(lls))
  } else {
    return(list("lls" = lls, "betas" = betas, "sses" = sses, "fits" = fits,
                "dfr" = dfr, "phis" = phis, "theta" = thetas))
  }
}

fima.ll.auto.donly <- function(pars, y, d.max = 1.5, Covar = NULL, ar = NULL, ma = NULL,
                               whi = FALSE, exact = TRUE, max.iter = Inf) {
  pars <- pars
  if (!is.null(ma)) {
    pars <- c(pars, ma)
    q <- length(ma)/ncol(y)
  } else {
    q <- 0
  }
  if (!is.null(ar)) {
    pars <- c(pars, ar)
    p <- length(ar)/ncol(y)
  } else {
    p <- 0
  }
  fima.ll.auto(pars, y = y, d.max = d.max, Covar = Covar, q = q, p = p, whi = whi,
               max.iter = max.iter)
}

fima.ll.auto.armaonly <- function(pars, y, d.max = 1.5, Covar = NULL, d,
                                  p = 0, q = 0,
                                  whi = FALSE, exact = TRUE, tr = TRUE, un = FALSE,
                                  max.iter = Inf) {
  pars <- c(d, pars)
  fima.ll.auto(pars, y = y, d.max = d.max, Covar = Covar, q = q, p = p,
               whi = whi, tr = tr, un = un, max.iter = max.iter)
}

#' @export
fima.ll.auto.iterative <- function(y, d.max = 1.5, Covar = NULL, p = 0, q = 0,
                                   eps = 10^(-7),
                                   print.iter = FALSE, whi = FALSE,
                                   exact = TRUE, d.min = -1.5,
                                   d.start = NULL, tr = TRUE,
                                   un = FALSE, max.iter = Inf) {

  if (is.matrix(y)) {
    k <- ncol(y)
  } else {
    k <- 1
    y <- matrix(y, nrow = length(y), ncol = 1)
  }

  opt.d <- optimize(fima.ll.auto.donly, interval = c(d.min, d.max - 10^(-4)), y = y, maximum = TRUE,
                    tol = .Machine$double.eps, d.max = d.max, Covar = Covar,
                    whi = whi, exact = exact, max.iter = max.iter)
  curr.d <- opt.d$maximum
  objs <- opt.d$objective

  if (p != 0 | q != 0) {
    if (!is.null(d.start)) {
      curr.d <- d.start
    } else {
      curr.d <- curr.d
    }
    init.fit <- apply(y, 2, function(yy) {
      arima(diffseries(yy, curr.d),
            order = c(p, 0, q), include.mean = FALSE, method = "ML")$coef
    })
    init.fit <- matrix(init.fit, nrow = q + p, ncol = k)


    if (q > 0) {
      init.ma.pars <- c(init.fit[1:q, ])
    }
    if (p > 0) {
      if (tr) {
        if (un) {
          init.ar.pars <- logit((((c(apply(init.fit[q + 1:p, , drop = FALSE], 2, ar.pacf)))) + 1)/2)
        } else {
          init.ar.pars <- ((c(apply(init.fit[q + 1:p, , drop = FALSE], 2, ar.pacf))))
        }

      } else {
        init.ar.pars <- c(init.fit[q + 1:p, , drop = FALSE])
      }
    }
    if (p > 0 & q > 0) {
      init.pars <- c(init.ma.pars, init.ar.pars)
    } else if (p == 0) {
      init.pars <- init.ma.pars
    } else {
      init.pars <- init.ar.pars
    }

    if (un) {
      lower.ar <- rep(-Inf, k*p)
      upper.ar <- rep(Inf, k*p)
    } else {
      lower.ar <- rep(-1, k*p)
      upper.ar <- rep(1, k*p)
    }

    opt.arma <- optim(par = init.pars,
                      fn = fima.ll.auto.armaonly,
                      lower = c(rep(-Inf, k*q), lower.ar),
                      upper = c(rep(Inf, k*q), upper.ar),
                      method = "L-BFGS-B",
                      y = y, d.max = d.max, Covar = Covar, q = q, p = p,
                      control = list("fnscale" = -1), d = curr.d,
                      whi = whi, exact = exact, tr = tr, un = un,
                      max.iter = max.iter)

    if (q == 0) {
      thetaval <- matrix(0, nrow = 1, ncol = k)
    } else {
      thetaval <- matrix(opt.arma$par[1:(k*q)], nrow = q, ncol = k)
    }

    if (p == 0) {
      pacfval <- phival <- matrix(0, nrow = 1, ncol = k)
    } else {
      if (tr) {
        if (un) {
          pacfval <- matrix(expit((opt.arma$par[k*q + 1:(k*p)]))*2 - 1, nrow = p, ncol = k)
        } else {
          pacfval <- matrix((opt.arma$par[k*q + 1:(k*p)]), nrow = p, ncol = k)
        }
        phival <- apply(pacfval, 2, pacf.ar)
      } else {
        phival <- matrix((opt.arma$par[k*q + 1:(k*p)]), nrow = p, ncol = k)
      }
    }

    old.obj <- opt.arma$value
    objs <- c(objs, old.obj)

    diff <- Inf
    count <- 0

    while (abs(diff) > eps) {

      conv <- 1
      if (!exact & count > 1) {
        opt.d <- optim(par = curr.d,
                       fn = fima.ll.auto.donly,
                       lower = d.min,
                       upper = d.max,
                       method = "L-BFGS-B",
                       y = y, d.max = d.max, Covar = Covar,
                       ar = phival, ma = thetaval,
                       control = list("fnscale" = -1),
                       whi = whi, exact = exact,
                       max.iter = max.iter)
        conv <- opt.d$convergence
      }
      if (conv == 0) {
        curr.d <- opt.d$par
        obj.val <- opt.d$value
      } else {
        opt.d <- optimize(fima.ll.auto.donly, interval = c(d.min, d.max - 10^(-4)), y = y,
                          maximum = TRUE,
                          tol = .Machine$double.eps, d.max = d.max,
                          Covar = Covar, ar = phival, ma = thetaval,
                          whi = whi, exact = exact,
                          max.iter = max.iter)
        curr.d <- opt.d$maximum
        obj.val <- opt.d$objective
      }

      objs <- c(objs, obj.val)
      if (print.iter) {
        cat("d=", round(curr.d, 3), "\n")
      }

      if (p != 0 | q != 0) {
        init.fit <- apply(y, 2, function(yy) {
          arima(diffseries(yy, curr.d),
                order = c(p, 0, q), include.mean = FALSE, method = "ML")$coef
        })
        init.fit <- matrix(init.fit, nrow = q + p, ncol = k)

        if (q > 0) {
          init.ma.pars <- c(init.fit[1:q, ])
        }
        if (p > 0) {
          if (tr) {
            if (un) {
              init.ar.pars <- logit((((c(apply(init.fit[q + 1:p, , drop = FALSE], 2, ar.pacf)))) + 1)/2)
            } else {
              init.ar.pars <- ((c(apply(init.fit[q + 1:p, , drop = FALSE], 2, ar.pacf))))
            }
          } else {
            init.ar.pars <- ((c(init.fit[q + 1:p, , drop = FALSE])))
          }
        }
        if (p > 0 & q > 0) {
          init.pars <- c(init.ma.pars, init.ar.pars)
        } else if (p == 0) {
          init.pars <- init.ma.pars
        } else {
          init.pars <- init.ar.pars
        }
      }

      opt.arma <- optim(par = c(init.pars),
                        fn = fima.ll.auto.armaonly,
                        lower = c(rep(-Inf, k*q), lower.ar),
                        upper = c(rep(Inf, k*q), upper.ar),
                        method = "L-BFGS-B",
                        y = y, d.max = d.max, Covar = Covar, q = q, p = p,
                        control = list("fnscale" = -1), d = curr.d,
                        whi = whi, exact = exact, tr = tr, un = un,
                        max.iter = max.iter)

      if (q == 0) {
        thetaval <- matrix(0, nrow = 1, ncol = k)
      } else {
        thetaval <- matrix(opt.arma$par[1:(k*q)], nrow = q, ncol = k)
      }

      if (p == 0) {
        pacfval <- phival <- matrix(0, nrow = 1, ncol = k)
      } else {
        if (tr) {
          if (un) {
            pacfval <- matrix(expit(opt.arma$par[k*q + 1:(k*p)])*2 - 1, nrow = p, ncol = k)
          } else {
            pacfval <- matrix((opt.arma$par[k*q + 1:(k*p)]), nrow = p, ncol = k)
          }
          phival <- apply(pacfval, 2, pacf.ar)
        } else {
          phival <- matrix((opt.arma$par[k*q + 1:(k*p)]), nrow = p, ncol = k)
        }
        if (print.iter) {
          cat("phi=", phival, "\n")
        }
      }

      diff <- abs(old.obj - opt.arma$value)
      old.obj <- opt.arma$value
      objs <- c(objs, old.obj)
      count <- count + 1
    }
  }

  ret <- curr.d
  if (q > 0) {
    ret <- c(ret, c(thetaval))
  }
  if (p > 0) {
    ret <- c(ret, c(phival))
  }
  return(list("pars" = ret, "objs" = objs))

}

#' @export
fima.ll.auto.exact <- function(y, d.max = 1.5, Covar = NULL, p = 0, q = 0,
                               eps = 10^(-7),
                               print.iter = FALSE, whi = FALSE,
                               d.min = -1.5,
                               tr = TRUE, by.val = 0.1, un = FALSE, max.iter = Inf) {

  if (is.matrix(y)) {
    k <- ncol(y)
  } else {
    k <- 1
    y <- matrix(y, nrow = length(y), ncol = 1)
  }

  ds <- seq(d.min, d.max, by = by.val)
  ds[length(ds)] <- ds[length(ds)] - 10^(-5)
  objs <- rep(NA, length(ds))
  phivals <- thetavals <- pars <- vector("list", length(ds))
  phivals <- lapply(phivals, function(x) {x <- rep(NA, p)})
  thetavals <- lapply(phivals, function(x) {x <- rep(NA, q)})
  pars <- lapply(phivals, function(x) {x <- rep(NA, p + q)})

  for (curr.d in ds[order(abs(ds), decreasing = FALSE)]) {
    if (print.iter) {cat("d=", curr.d, "\n")}

    init.fit <- NULL
    if (p != 0 | q != 0) {

      skip <- FALSE
      if (curr.d != 0) {
        if (curr.d > 0) {
          skip <- is.na(objs[which(curr.d == ds) - 1])
        } else {
          skip <- is.na(objs[which(curr.d == ds) + 1])
        }
      }

      if (!skip) {
        new.start <- curr.d == 0
        # if (!new.start) {
        #   new.start <- 1 %in% abs(phival)
        # }
        if (new.start) {
          # init.fit <- apply(y, 2, function(yy) {
          #   arima(diffseries(yy, curr.d),
          #         order = c(p, 0, q), include.mean = FALSE, method = "ML")$coef
          # })
          # init.fit <- matrix(init.fit, nrow = q + p, ncol = k)
          init.fit <- matrix(0, nrow = q + p, ncol = k)
        } else {
          if (curr.d > 0) {
            if (curr.d == min(ds[ds > 0])) {
              init.fit <- matrix(pars[[which(curr.d == ds) - 1]], nrow = q + p, ncol = k)
            } else {
              init.fit <- matrix(pars[[which(curr.d == ds) - 1]] + pars[[which(curr.d == ds) - 1]] - pars[[which(curr.d == ds) - 2]], nrow = q + p, ncol = k)
            }
          } else {
            if (curr.d == max(ds[ds < 0])) {
              init.fit <- matrix(pars[[which(curr.d == ds) + 1]], nrow = q + p, ncol = k)
            } else {
              init.fit <- matrix(pars[[which(curr.d == ds) + 1]] + pars[[which(curr.d == ds) + 1]] - pars[[which(curr.d == ds) + 2]], nrow = q + p, ncol = k)
            }
          }
        }

        if (q > 0) {
          init.ma.pars <- 0 # c(init.fit[1:q, ])
        }
        if (p > 0) {
          if (tr) {
            if (un) {
              init.ar.pars <- logit((((c(apply(init.fit[q + 1:p, , drop = FALSE], 2, ar.pacf)))) + 1)/2)
            } else {
              init.ar.pars <- ((c(apply(init.fit[q + 1:p, , drop = FALSE], 2, ar.pacf))))
            }
          } else {
            init.ar.pars <- c(init.fit[q + 1:p, , drop = FALSE])
          }
        }
        if (p > 0 & q > 0) {
          init.pars <- c(init.ma.pars, init.ar.pars)
        } else if (p == 0) {
          init.pars <- init.ma.pars
        } else {
          init.pars <- init.ar.pars
        }


        if (un) {
          lower.ar <- rep(-Inf, k*p)
          upper.ar <- rep(Inf, k*p)
        } else {
          lower.ar <- rep(-1, k*p)
          upper.ar <- rep(1, k*p)
        }

        try(opt.arma <- optim(par = init.pars,
                              fn = fima.ll.auto.armaonly,
                              lower = c(rep(-Inf, k*q), lower.ar),
                              upper = c(rep(Inf, k*q), upper.ar),
                              method = "L-BFGS-B",
                              y = y, d.max = d.max, Covar = Covar, q = q, p = p,
                              control = list("fnscale" = -1), d = curr.d,
                              whi = whi, exact = exact, tr = tr, un = un, max.iter = max.iter),
            silent = TRUE)
        fail <- FALSE
        if (!curr.d == 0) {
          if (curr.d > 0) {
            fail <- opt.arma$value ==  objs[which(curr.d == ds) - 1]
          } else {
            fail <- opt.arma$value ==  objs[which(curr.d == ds) + 1]
          }
        }
        if (!fail) {
          objs[which(curr.d == ds)] <- opt.arma$value
          pars[[which(curr.d == ds)]] <- opt.arma$par

          if (q == 0) {
            thetaval <- matrix(0, nrow = 1, ncol = k)
          } else {
            thetaval <- matrix(opt.arma$par[1:(k*q)], nrow = q, ncol = k)
            thetavals[[which(curr.d == ds)]] <- thetaval
          }


          if (p == 0) {
            pacfval <- phival <- matrix(0, nrow = 1, ncol = k)
          } else {
            if (tr) {
              if (un) {
                pacfval <- matrix(expit(opt.arma$par[k*q + 1:(k*p)])*2 - 1, nrow = p, ncol = k)
              } else {
                pacfval <- matrix((opt.arma$par[k*q + 1:(k*p)]), nrow = p, ncol = k)
              }
              phival <- apply(pacfval, 2, pacf.ar)
            } else {
              phival <- matrix((opt.arma$par[k*q + 1:(k*p)]), nrow = p, ncol = k)
            }
            phivals[[which(curr.d == ds)]] <- phival
            if (sum(abs(phival) == 1) > 0) {
              objs[which(curr.d == ds)] <- NA
            }
            if (print.iter) {
              cat("phi=", phival, "\n")
            }
          }
        }
      }
    }


    else {
      objs[which(curr.d == ds)] <- fima.ll.auto.donly(pars = curr.d,
                                                      y = y,
                                                      d.max = d.max, Covar = Covar,
                                                      whi = whi, exact = exact,
                                                      max.iter = max.iter)
    }

  }

  ret <- ds[which(objs == max(objs, na.rm = TRUE))]
  if (q > 0) {
    ret <- c(ret, c(thetavals[[which(objs == max(objs, na.rm = TRUE))]]))
  }
  if (p > 0) {
    ret <- c(ret, c(phivals[[which(objs == max(objs, na.rm = TRUE))]]))
  }
  return(list("pars" = ret, "objs" = objs, "ds" = ds, "pars"=pars, "phis" = phivals))

}


# fima.ll.auto.mcmc <- function(y, d.max = 1.5, Covar = NULL, p = 0, q = 0,
#                               print.iter = FALSE, whi = FALSE,
#                               exact = TRUE, d.min = -1.5,
#                               samps = 1000) {
#
#
# }


