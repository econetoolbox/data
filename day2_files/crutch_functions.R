exponent.removal<-function (fw, i_index){
    d1 <- as.data.frame(degree(fw))
    kmax <- max(d1$`degree(fw)`)
    kmin <- min(d1$`degree(fw)`)
    k_vector <- sort(unique(d1$`degree(fw)`))
    colnames_Pe <- paste0("Pe_", i_index)
    Pe_results <- as.data.frame(matrix(ncol = length(colnames_Pe), 
        nrow = nrow(d1)))
    Pe_results <- cbind(d1, Pe_results)
    colnames(Pe_results)[-1] <- colnames_Pe
    for (j in 1:nrow(d1)) {
        current_species_k <- d1[j, ]
        Nk <- sum(d1$`degree(fw)` == current_species_k)
        for (i in 1:length(i_index)) {
            current_i_value <- i_index[i]
            sum_denominator <- as.data.frame(matrix(nrow = length(k_vector)))
            sum_denominator <- cbind(k_vector, sum_denominator)
            for (f in 1:nrow(sum_denominator)) {
                Ni <- sum(d1$`degree(fw)` == sum_denominator[f, 
                  1])
                sum_denominator[f, 2] <- ((1 - current_i_value)^(kmax - 
                  sum_denominator[f, 1])) * Ni
            }
            sum_denominator <- sum(sum_denominator$V1)
            Pe <- (((1 - current_i_value)^(kmax - current_species_k)) * 
                Nk)/sum_denominator
            Pe_results[j, i + 1] <- Pe
        }
    }
    return(Pe_results[, -1])
}

iterate<-function (fw_to_attack, probs_of_fw, alpha1, iter, i_index, plot = FALSE, export_plot = FALSE, plot_name = NULL){
    result_iterate <- data.frame(matrix(nrow = ncol(probs_of_fw)))
    for (i in 1:iter) {
        r1 <- robustness(fw_to_attack, probs_of_fw, alpha1 = 50)
        R1 <- r1$Ralpha
        result_iterate <- cbind(result_iterate, R1)
        message(paste0("Iteration ", i))
    }
    result_iterate <- result_iterate[, -1]
    meanR <- apply(result_iterate, 1, FUN = mean)
    sdR <- apply(result_iterate, 1, FUN = sd)
    output <- as.data.frame(cbind(i_index, meanR, sdR))
    output.se <- output$sdR/sqrt(nrow(output))
    margin.error <- qnorm(0.975) * output.se
    lower.bound <- output$meanR - margin.error
    upper.bound <- output$meanR + margin.error
    output <- data.frame(output, lower.bound, upper.bound)
    if (any(output$lower.bound < 0)) 
        output[output$lower.bound < 0, ]$lower.bound <- 0
    if (plot == TRUE) {
        print(ggplot(output, aes(x = i_index, y = meanR), xlab = "label") + 
            xlab("Intentionality (I)") + ylab(paste0("R", alpha1)) + 
            ylim(0, (alpha1/100) + 0.1) + geom_line(color = "steelblue4", 
            lwd = 1) + geom_ribbon(alpha = 0.5, aes(ymin = lower.bound, 
            ymax = upper.bound), fill = "steelblue2", color = "steelblue2"))
    }
    if (export_plot == TRUE) {
        png(paste0(plot_name, ".png"), width = 500, height = 400)
        print(ggplot(output, aes(x = i_index, y = meanR), xlab = "label") + 
            xlab("Intentionality (I)") + ylab(paste0("R", alpha1)) + 
            ylim(0, (alpha1/100) + 0.1) + geom_line(color = "steelblue4", 
            lwd = 1) + geom_ribbon(alpha = 0.5, aes(ymin = lower.bound, 
            ymax = upper.bound), fill = "steelblue2", color = "steelblue2"))
        dev.off()
    }
    return(output)
}

dd.fw<-function (list1, log = TRUE, cumulative = TRUE) {
    if (class(list1[[1]]) == "list") {
        list2 <- list1[[1]]
    }
    else list2 <- list1
    df_final <- data.frame()
    for (i in 1:length(list2)) {
        m1 <- list2[[i]]
        m1 <- as.matrix(m1)
        g1 <- igraph::graph_from_adjacency_matrix(m1, weighted = NULL, 
            mode = "undirected")
        g2 <- igraph::degree_distribution(g1, cumulative)
        d <- igraph::degree(g1, mode = "all")
        degree1 <- 1:max(d)
        probability <- g2[-1]
        nonzero.position <- which(probability != 0)
        probability <- (probability[nonzero.position])
        degree1 <- (degree1[nonzero.position])
        iter <- rep(paste0("iter", i), length(degree1))
        colour1 <- rep(randomColor(), length(iter))
        df0 <- data.frame(iter, degree1, probability, colour1)
        df_final <- rbind(df_final, df0)
    }
    if (log == TRUE) {
        print(ggplot2::ggplot(df_final, aes(x = degree1, y = probability, 
            group = iter)) + geom_line(aes(col = factor(iter))) + 
            theme(legend.position = "none") + labs(title = "Degree distribution (log-log)", 
            x = "degree (log)", y = "Probability (log)") + theme(plot.title = element_text(hjust = 0.5)) + 
            scale_y_log10() + scale_x_log10() + annotation_logticks())
    }
    if (log == FALSE) {
        print(ggplot2::ggplot(df_final, aes(x = degree1, y = probability, 
            group = iter)) + geom_line(aes(col = factor(iter))) + 
            theme(legend.position = "none") + labs(title = "Degree distribution", 
            x = "degree", y = "Probability") + theme(plot.title = element_text(hjust = 0.5)))
    }
    return(df_final[, -4])
}