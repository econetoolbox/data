library(bipartite)
library(igraph)
#library(FWebs)
library(vegan)
library(cheddar)
#library(matlib)
library(sbm)
library(alluvial)
library(econetwork)
library(poweRlaw)
library(NetIndices)
library(ggplot2)
library(rnetcarto)
#library(maxnodf)
#library(NetworkExtinction)

### Simulating food webs

cascade_matrix<-function(cc,nspecies){ #from Cohen-Newman-Briand's papers
	upper.tri(matrix(1,nrow=nspecies,ncol=nspecies), diag = FALSE)*matrix(rbinom(nspecies*nspecies,1,cc/nspecies),nrow=nspecies)
}

niche_matrix<-function(connectance,nspecies){ #Williams-Martinez model
	n_i<-runif(nspecies)
	r_i<-rbeta(nspecies,1,(1/(2*connectance))-1)
	r_i<-r_i*n_i
	c_i<-sapply(1:nspecies,function(x) runif(1,min=r_i[x]/2,max=n_i[x]))
	pred_function<-function(z_1,z_2){
		if((n_i[z_1]<=c_i[z_2]+0.5*r_i[z_2])&(n_i[z_1]>=c_i[z_2]-0.5*r_i[z_2])) {
			1
		}
		else{
			0
		}
	}
	mat<-sapply(1:nspecies,function(x) sapply(1:nspecies,function(y) pred_function(y,x)))
	list("matrix"=mat,"n"=n_i,"r"=r_i,"c"=c_i)
}

generate_DM_model<-function(n,prop_basal,quant_fun="qpois", ...){#generating the Dubart-Massol food web model (Massol et al. 2017)
	basal<-round(n*prop_basal)
	degs<-generate_degseq_unipartite(n,quant_fun,...)
	undirected<-sample_degseq(degs, method = "vl")
	gvc<-greedy_vertex_coloring(undirected)
	majority_color<-which(gvc==which.max(table(gvc)))
	if(length(majority_color)<basal){
		print("not enough nodes in the largest color to make basal species, ")
		print("the number of basal species is set to")
		print(length(majority_color))
		basal<-length(majority_color)
	}
	basal_sp<-sample(majority_color,basal)
	tr_levels<-apply(distances(undirected,v=basal_sp),2,min_without_inf)
	chain_length<-max(tr_levels)
	directed<-as.directed(undirected)
	for(i in 1:chain_length){
		previous_set<-which(tr_levels==i-1)
		current_set<-which(tr_levels==i)
		directed<-delete_edges(directed,E(directed) [current_set %->% previous_set])
	}
	mut_edges<-which_mutual(directed)
	directed_intraguild<-as.directed(as.undirected(subgraph.edges(directed,E(directed)[mut_edges],delete.vertices = FALSE)),mode="random")
	directed<-delete_edges(directed,E(directed) [mut_edges])
	directed<-union(directed,directed_intraguild)
	return(directed)
}

make_food_web_from_undirected<-function(undirected,basal){
	gvc<-greedy_vertex_coloring(undirected)
	majority_color<-which(gvc==which.max(table(gvc)))
	if(length(majority_color)<basal){
		print("not enough nodes in the largest color to make basal species, ")
		print("the number of basal species is set to")
		print(length(majority_color))
		basal<-length(majority_color)
	}
	basal_sp<-sample(majority_color,basal)
	tr_levels<-apply(distances(undirected,v=basal_sp),2,min_without_inf)
	chain_length<-max(tr_levels)
	directed<-as_directed(undirected)
	for(i in 1:chain_length){
		previous_set<-which(tr_levels==i-1)
		current_set<-which(tr_levels==i)
		directed<-delete_edges(directed,E(directed) [current_set %->% previous_set])
	}
	mut_edges<-which_mutual(directed)
	directed_intraguild<-as_directed(as_undirected(subgraph_from_edges(directed,E(directed)[mut_edges],delete.vertices = FALSE)),mode="random")
	directed<-delete_edges(directed,E(directed) [mut_edges])
	directed<-union(directed,directed_intraguild)
	return(directed)
}


### Simulating a (B_)EDD network

leqone_mat<-function(x){# x is a matrix #function to generate a matrix of positive elements always less than 1
	d<-dim(x)
	matrix(sapply(x,function(u) ifelse(u>1,1,u)),nrow=d[1],ncol=d[2])
}

SimulB_EDD <- function(m, n, rho, lambda.g, lambda.h){#m is the number of row species, n the nb of column, rho the connectance, lambda.g the parameter for the rows, lambda.h for the columns, Ouadah-Latouche-Robin's algo
   # Simulation of B-EDD
   u <- runif(m); v <- runif(n)
   p <- rho * (lambda.g * u^(lambda.g-1)) %o% (lambda.h * v^(lambda.h-1))
   p<-leqone_mat(p)
   return(list(u=u, v=v, prob=p, net=matrix(rbinom(n*m, 1, p), m, n)))
}

Simul_EDD <- function(m, rho, lambda){#m is the number of  species, rho the connectance, lambda the parameter, Ouadah-Latouche-Robin's algo
   # same as above for EDD (unipartite graphs)
   u <- runif(m); 
   p <- rho * (lambda * u^(lambda-1)) %o% (lambda * u^(lambda-1))
   p<-leqone_mat(p)
   res<-matrix(rbinom(m*m, 1, p), m, m)
   res[lower.tri(res,diag=T)] <- 0
   res <- res + t(res)
   return(list(u=u, prob=p, net=res))
}

randomize.BChungLu<-function(bipmat){ #bipmat is an existing bipartite matrix, the function randomizes it with the aim of keeping the expected degrees
  s<-sum(bipmat)
  m1<-apply(bipmat,1,sum)
  m2<-apply(bipmat,2,sum)
  if(max(m1)*max(m2) > s) {
    print("Warning, some probabilities are higher than 1")
  }
  p<-leqone_mat(m1%o%m2/s)
  apply(p,c(1,2),function(x) rbinom(1,size = 1,prob = min(x,1)))
}


randomize.BEDD<-function(bipmat){ #same as Chung-Lu, but using distributions of degrees rather than actual degrees
	s<-sum(bipmat)
	m1<-apply(bipmat,1,sum)
	d1<-length(m1)
	m2<-apply(bipmat,2,sum)
	d2<-length(m2)
	rho<-s/(d1*d2)
	mset1<-ecdf(m1*d2/s)
	mset2<-ecdf(m2*d1/s)
	sample1<-quantile(mset1,probs=runif(d1))
	sample2<-quantile(mset2,probs=runif(d2))
	p <- rho * sample1 %o% sample2
	p<-leqone_mat(p)
	matrix(rbinom(d1*d2, 1, p), d1, d2)
}

randomize.wBEDD_poisson<-function(bipmat){ #randomization for a weighted BEDD following a Poisson distribution
	s<-sum(bipmat)
	m1<-apply(bipmat,1,sum)
	d1<-length(m1)
	m2<-apply(bipmat,2,sum)
	d2<-length(m2)
	rho<-s/(d1*d2)
	mset1<-ecdf(m1*d2/s)
	mset2<-ecdf(m2*d1/s)
	sample1<-quantile(mset1,probs=runif(d1))
	sample2<-quantile(mset2,probs=runif(d2))
	p <- rho * sample1 %o% sample2
	par(mfrow=c(3,2))
	plot(mset1)
	plot(mset2)
	plot(density(m1))
	plot(density(m2))
	plot(density(apply(p,1,sum)))
	plot(density(apply(p,2,sum)))
	res<-matrix(rpois(d1*d2, p), d1, d2)
	if(one_component(res)){ 
		res
	}
	else{
		randomize.wBEDD_poisson(bipmat)
	}
}

randomize.wBEDD_ZIP<-function(bipmat){ #randomization for a weighted BEDD following a Zero-Inflated Poisson distribution
	s<-sum(bipmat)
	m1<-apply(bipmat,1,sum)
	d1<-length(m1)
	m2<-apply(bipmat,2,sum)
	d2<-length(m2)
	mu<-mean((as.vector(bipmat)))
	v<-var((as.vector(bipmat)))
	lambda<-mu-1+(v/mu)
	pz<-(v-mu)/(v+mu^2-mu)
	mset1<-ecdf(m1*d2/s)
	mset2<-ecdf(m2*d1/s)
	sample1<-quantile(mset1,probs=runif(d1))
	sample2<-quantile(mset2,probs=runif(d2))
	p <- lambda * sample1 %o% sample2
	nz<- check_mat(pz * rep(1,d1) %o% rep(1,d2))
	res<-matrix(rbinom(d1*d2,1,1-nz)*rpois(d1*d2, p), d1, d2)
	if(one_component(res)){ 
		res
	}
	else{
		randomize.wBEDD_ZIP(bipmat)
	}
}


randomize.EDD<-function(graph){ #same as above on undirected graphs
	if(igraph::is_directed(graph)){
		graph<-igraph::as.undirected(graph)
	}
	adjmat<-igraph::as_adj(graph,sparse=FALSE)
	s<-sum(adjmat)
	m<-apply(adjmat,1,sum)
	d<-dim(adjmat)[1]
	rho<-2*s/(d*(d-1))
	mset<-ecdf(m*d/s)
	sample_expdegs<-quantile(mset,probs=runif(d))
	p <- rho * sample_expdegs %o% sample_expdegs
	p<-leqone_mat(p)
	res<-matrix(rbinom(d*d, 1, p), d, d)
	res[lower.tri(res,diag=T)] <- 0
	res <- res + t(res)
	igraph::graph_from_adjacency_matrix(res)
}


generate.ChungLu<-function(ED1,ED2){ #ED1 and ED2 are the vectors of expected degrees
  s1<-sum(ED1)
  s2<-sum(ED2)
  if(s1 != s2) {
    print("Warning, the two sequences have different sums")
  }
  s<-max(s1,s2)
  if(max(ED1)*max(ED2) > s) {
    print("Warning, some probabilities are higher than 1")
  }
  p<-leqone_mat(ED1%o%ED2/s)
  apply(p,c(1,2),function(x) rbinom(1,size = 1,prob = min(x,1)))
}


### bipartite utilities

union_bipartite<-function(list_nets){
	x<-do.call(igraph::union, list_nets)
	l<-length(list_nets)
	type_vec<-sapply(1:l,function(y) paste0("type_",y))
	or_types<-apply(sapply(1:l, function(k) igraph::vertex_attr(x, type_vec[k])),1,any)
	V(x)$type<-!(is.na(or_types)|!(or_types))
	x
}

### food web utilities

# for classic trophic level computations, use the 'cheddar' package, for instance ShortestTrophicLevel

as_Community<-function(network,net_name="."){#takes a directed network (with species names) and make it a Community object for cheddar
	names_net<-V(network)$name
	nodes<-data.frame("node"=names_net,row.names= names_net)
	properties=list("title"=net_name)
	tlinks<-igraph::as_long_data_frame(network)
	trophic.links<-as.matrix(tlinks[,c("from_name","to_name")])
	colnames(trophic.links)<-c("resource", "consumer")
	cheddar::Community(nodes, properties, trophic.links)
}
#example: ShortestTrophicLevel(as_Community(network,"WTF"))

trophic_levels<-function(network) { #based on MacKay et al. 2020
	lap<-corrected_laplacian(network)
	imbalance<-igraph::degree(network,mode="in")-igraph::degree(network,mode="out")
	solve(as.matrix(lap)) %*% imbalance
}

alt_TL<-function(network){ #yet another implementation of trophic levels
	undir_net<-igraph::as_undirected(network)
	basals<-which(igraph::degree(network,mode="in")==0)
	dist_mat<-t(igraph::distances(network,v=which(igraph::degree(network,mode="in")==0),mode="out"))
	s<-dim(dist_mat)[1]
	shortest_chain<-sapply(1:s,function(x) min_without_inf(dist_mat[x,]))+1
	longest_chain<-sapply(1:s,function(x) max_without_inf(dist_mat[x,]))+1
	average_chain<-sapply(1:s,function(x) mean_without_inf(dist_mat[x,]))+1
	if(!is.null(V(network)$name)){
		res<-data.frame("species"=V(network)$name,"shortest"=shortest_chain,"longest"=longest_chain,"average" = average_chain)
	}
	else{
		res<-data.frame("shortest"=shortest_chain,"longest"=longest_chain,"average" = average_chain)
	}
	res
}

FW_interaction_from_predation<-function(mat,rho){
	n<-dim(mat)[1]
	fill<-faux::rnorm_multi(n*(n-1)/2,2,r=rho)
	ut<-matrix(0,n,n)
	ut[lower.tri(ut,diag = FALSE)]<-fill[,1]
	ut<-mat*t(ut)
	lt<-matrix(0,n,n)
	lt[lower.tri(lt, diag = FALSE)]<-fill[,2]
	lt<-(t(mat))*lt
	ut+lt
}

layout_as_food_web<-function(network){#adapted from Jon Borelli's code https://assemblingnetwork.wordpress.com/2013/04/03/more-food-web-plotting-with-r/
	l<-length(V(network))
	lay<-matrix(nrow=l,ncol=2) 
	lay[,1]<-igraph::layout_with_graphopt(network)[,1]
	lay[,2]<-TrophicLevels(as_Community(network))[,5]-1
	lay
}

layout_as_food_web2<-function(network){#adapted from Jon Borelli's code https://assemblingnetwork.wordpress.com/2013/04/03/more-food-web-plotting-with-r/
	l<-length(V(network))
	lay<-matrix(nrow=l,ncol=2) 
	lay[,1]<-igraph::layout_with_graphopt(network)[,1]
	lay[,2]<-trophic_levels(network)
	lay
}

layout_as_food_web3<-function(network){#adapted from Jon Borelli's code https://assemblingnetwork.wordpress.com/2013/04/03/more-food-web-plotting-with-r/
	l<-length(V(network))
	lay<-matrix(nrow=l,ncol=2) 
	lay[,1]<-igraph::layout_with_graphopt(network)[,1]
	lay[,2]<-alt_TL(network)[,3]
	lay
}

layout_as_food_web3bis<-function(network){
	l<-length(V(network))
	lay<-matrix(nrow=l,ncol=2) 
	lay[,2]<-alt_TL(network)[,3]
	n<-table(lay[,2])
	vals<-sort(unique(lay[,2]))
	for(i in 1:length(n)){
		locations<-which(lay[,2]==vals[i])
		lay[locations,1]<-(1:n[i])/n[i]
	}
	lay
}

layout_as_food_web4<-function(network){
	graphlayouts::layout_with_constrained_stress(network,coord = alt_TL(network)[,3],fixdim = "y")
}

layout_as_food_web5<-function(network){
	igraph::layout_with_gem(network,coords=layout_as_food_web3(network))
}



### other utilities

automatic_naming<-function(network){
	n<-igraph::gorder(network)
	net<-network
	V(net)$name<-sapply(1:n,function(x) paste0("sp_",x))
	net
}

min_without_inf<-function(vec){
	min(vec[!is.infinite(vec)])
}

max_without_inf<-function(vec){
	max(vec[!is.infinite(vec)])
}

mean_without_inf<-function(vec){
	mean(vec[!is.infinite(vec)])
}

p.val<-function(test_val,test_collection,method="larger",label=""){#compute a p-value for a test based on a collection of values simulated using a null model
	test_collection<-c(test_collection,test_val)
	n<-length(test_collection)
	cumul<-ecdf(test_collection)
	mmin<-min(test_collection)
	mmax<-max(test_collection)
	plot(density(test_collection),xlim=c(mmin,mmax),main=label,xlab="")
	abline(v=test_val,col="red")
	if(method=="lower"){
		max(cumul(test_val),1/n)
	}
	else if(method=="two-sided"){
		max(2*min(cumul(test_val),1-cumul(test_val)),1/n)
	}
	else{
		max(1-cumul(test_val),1/n)
	}
	
}

series_randomize<-function(mat,randomization,nsim = 100){#function to obtain a collection of null matrices from a single one. randomization should be a character string indicating the null model function (e.g. "randomize.wBEDD_poisson")
	dd<-c(dim(mat),nsim)
	f<-get(randomization)
	res.list<-lapply(1:nsim,function(x) f(mat))
	array(unlist(res.list),dim=dd)
}

corrected_laplacian<-function(network){
	lap<-igraph::laplacian_matrix(network)
	lap+diag(degree(network,mode="in"))
}

to_upper_triangular<-function(mat){
	upper.tri(mat, diag = FALSE)*mat
}

thresh_mat<-function(x, threshold){# x is a matrix #function to generate a binary matrix based on a minimum threshold
	d<-dim(x)
	matrix(sapply(x,function(u) ifelse(u>threshold,1,u)),nrow=d[1],ncol=d[2])
}

make_alluvial_2<-function(classif1,classif2,name1,name2){
	A <- as.data.frame(table(classif1,classif2))
	colnames(A) = c(name1,name2,"Freq")
	w   <- which(A$Freq != 0)
	A <- A[w,]
	alluvial::alluvial(A[,c(1,2)],freq = A$Freq)
}

qtrunc <- function(p, spec, a = -Inf, b = Inf, ...){#copied from Nadarajah & Kotz 2006
	tt <- p
	G <- get(paste("p", spec, sep = ""), mode = "function")
	Gin <- get(paste("q", spec, sep = ""), mode = "function")
	tt <- Gin(G(a, ...) + p*(G(b, ...) - G(a, ...)), ...)
	return(tt)
}

spectral_clustering <- function(graph, nb_cluster, normalize = "symmetric") {#from J. Chiquet's git page https://jchiquet.github.io/MAP566/docs/mixture-models/map566-lecture-graph-clustering-part1.html
  
  ## Compute Laplacian matrix
  L <- igraph::laplacian_matrix(graph, normalization = normalize) 
  ## Generates indices of last (smallest) K vectors
  selected <- rev(1:ncol(L))[1:nb_cluster] 
  ## Extract n normalized eigen-vectors
  U <- eigen(L)$vectors[, selected, drop = FALSE]  # spectral decomposition
  U <- sweep(U, 1, sqrt(rowSums(U^2)), '/')    
  ## Perform k-means
  res <- kmeans(U, nb_cluster, nstart = 40)$cl
  
  res
}

laplacian_spectral_gap<- function(graph, normalize = "symmetric"){
	L <- igraph::laplacian_matrix(graph, normalization = normalize)
	comps<-igraph::count_components(graph)
	lambdas <- sort(eigen(L)$values)
	l<-length(lambdas)
	s_gaps<-lambdas[-1]-lambdas[-l]
	s_util<-s_gaps[-(1:comps)]
	s_util<-s_util[1:round(l/2)]
	opt_n<-which.max(s_util)+comps
	
	par(mfrow=c(2,1))
	plot(lambdas,xlab="",ylab="lambda",type="l")
	plot(s_gaps,xlab="",ylab="spectral gap",type="l")
	
	list("spectral_gaps"=s_gaps,"optim_n"=opt_n)
}

### degree sequence utilities
generate_degseq_unipartite_old<-function(n,quant_fun="qpois", ...){
	p_s<-(1:n-0.5)/n
	d_s<-get(quant_fun)(p=p_s,...)
	if(!igraph::is_graphical(d_s)){
		sp<-substring(quant_fun,first=2)
		trun<-1
		while(!is_graphical(d_s)){
			trun<-trun+1
			d_s<-qtrunc(p=p_s,spec = sp, a=trun, ...)
		}
		d_s
	}
	else{
		d_s
	}
}

generate_degseq_unipartite<-function(n,quant_fun="qpois", ...){
	p_s<-(1:n-0.5)/n
	d_s<-get(quant_fun)(p=p_s,...)
	if(d_s[1]==0){
		sp<-substring(quant_fun,first=2)
		trun<-1
		d_s<-qtrunc(p=p_s,spec = sp, a=trun, ...)
		while(!is_graphical(d_s)){
			temp<-sum(d_s[1:(n-1)])
			if(d_s[n] > temp){
				d_s[n]<-sum(d_s[1:(n-1)])
			}
			else{
				d_s[n]<-d_s[n]+1
			}
		}
		d_s
	}
	#print(d_s)
	else if(!igraph::is_graphical(d_s)){
		temp<-sum(d_s[1:(n-1)])
		if(d_s[n] > temp){
			d_s[n]<-sum(d_s[1:(n-1)])
		}
		else{
			d_s[n]<-d_s[n]+1
		}
		d_s
	}
	else{
		d_s
	}
}

### configuration model

config_VL<-function(graph,nsim = 100){#configuration model for binary networks; built upon vegan and igraph
	if(igraph::is_igraph(graph)){
		if((igraph::is_weighted(graph))||(!igraph::is_simple(graph))){
			print("graph is not simple, can't do")
		}
		else if(igraph::is_bipartite(graph)){
			print("bipartite graph detected")
			incidence<-as.matrix(igraph::as_biadjacency_matrix(graph))
			configs<-simulate(vegan::nullmodel(incidence,"curveball"),nsim=nsim) 
			lapply(1:nsim,function(x) igraph::graph_from_biadjacency_matrix(configs[,,x]))
		}
		else{
			print("unipartite graph detected")
			lapply(1:nsim, function(x) igraph::sample_degseq(igraph::degree(graph), method = "vl"))
		}
	}
	else if(is.matrix(graph)){
		d<-dim(graph)
		if(max(graph)>1){
			print("graph is not simple, can't do")
		}
		else if(d[1]==d[2]){
			print("unipartite graph detected")
			config_VL(graph_from_adjacency_matrix(graph),nsim)
		}
		else{
			print("bipartite graph detected")
			configs<-simulate(vegan::nullmodel(graph,"curveball"),nsim=nsim) 
			lapply(1:nsim,function(x) igraph::graph_from_biadjacency_matrix(configs[,,x]))
		}
	}
	else{
		config_VL(as.matrix(graph),nsim)
	}
}

##clustering with rnetcarto

cluster_netcarto<-function(g,...){
	adj<-as_adj(g,sparse=FALSE)
	netcarto_res<-netcarto(adj,...)
	indices<-match(V(g)$name,netcarto_res[[1]]$name)
	make_clusters(g,membership = 1+netcarto_res[[1]][indices,2],algorithm = "netcarto", modularity = netcarto_res[[2]])
}

## salvaged (and corrected) from FWebs

exponent.removal<-function (crit_vector, i_index){
    d1 <- as.data.frame(crit_vector)
	s<-nrow(d1)
	n<-length(i_index)
	
	colindices<-matrix(rep(1:n,each=s),ncol= n, nrow = s)
	rowindices<-matrix(rep(1:s,times=n),ncol= n, nrow = s)
	temp_Pe<-matrix(sapply(1:(n*s),function(x) (1-i_index[colindices[x]])^(-d1[rowindices[x],1])),ncol= n, nrow = s)
	temp_Pe_col_sums<-apply(temp_Pe,2,sum)
	
    colnames_Pe <- paste0("Pe_", i_index)
	Pe_mat <-temp_Pe/(rep(1,s)%*%t(temp_Pe_col_sums))
    Pe_results <- as.data.frame(Pe_mat)
    colnames(Pe_results) <- colnames_Pe
	rownames(Pe_results)<-rownames(d1)
    return(Pe_results)
}

plot.iterate_logscale<-function(output,alpha1=50){
	ggplot(output, aes(x = i_index, y = meanR), xlab = "label") + xlab("Intentionality (I)") + ylab(paste0("R", alpha1)) + ylim(0, (alpha1/100) + 0.1) + geom_line(color = "steelblue4", lwd = 1) + geom_ribbon(alpha = 0.5, aes(ymin = lower.bound, ymax = upper.bound), fill = "steelblue2", color = "steelblue2")+ scale_y_continuous(trans='log10')
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
            mode = "max")
        g2 <- igraph::degree_distribution(g1, cumulative)
        d <- igraph::degree(g1, mode = "all")
        degree1 <- 1:max(d)
        probability <- g2[-1]
        nonzero.position <- which(probability != 0)
        probability <- (probability[nonzero.position])
        degree1 <- (degree1[nonzero.position])
        iter <- rep(paste0("iter", i), length(degree1))
        colour1 <- rep(randomcoloR::randomColor(), length(iter))
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

create.fw.list<-function (db, folder = NULL, ecosyst = FALSE, ref = FALSE, spatial = FALSE, code = FALSE, mangal_types = NULL){
    model.dissemination_allow <- model.whole_food_web <- NULL
    fwlist <- list()
    if (!db %in% c("eb", "wl", "gw", "mg")) 
        stop("Argument 'db' must take one of the following values:\n\n                                          'wl' - Web of Life\n                                          'mg' - mangal\n                                          'gw' - globalweb\n                                          'eb' - ecobase")
    if (!db %in% c("wl", "gw") & !is.null(folder)) 
        stop("Argument 'folder'can only be used if 'db'= 'wl' or 'gw'!")
    if (!db %in% c("mg") & !is.null(mangal_types)) 
        stop("Argument 'type'can only be used if 'db'= 'mg'!")
    if (!db %in% c("gw", "eb") & ecosyst == TRUE) 
        stop("Argument 'ecosyst'can only be used if 'db'= 'eb' or 'gw'!")
    if (!db %in% c("wl", "mg", "eb") & spatial == TRUE) 
        stop("Argument 'spatial'can only be used if 'db'= 'eb', 'mg' 'wl'!")
    if (!db %in% c("wl", "mg", "gw") & code == TRUE) 
        stop("Argument 'code'can only be used if 'db'= 'wl', 'mg'', 'gw'!")
    if ("mg" %in% db & is.null(mangal_types)) 
        message("No value defined for the 'mangal_types' argument! \n Will assume types 'predation' and 'herbivory'.")
    if (!"mg" %in% db & !is.null(mangal_types)) 
        stop("Argument 'mangal_types'can only be used if 'db'= 'mg'!")
    if (db == "gw") {
        message("####################### GLOBALWEB DATABASE #######################\n\n")
        message("Fetching info from the provided folder!")
        files_gw <- list.files(path = folder, pattern = "WEB")
        ngw <- length(files_gw)
        message(paste0("There are ", ngw, " food web files in the folder!"))
        message("You should have downloaded the file 'Current Food Web List' from the GlobalWeb website\n             \n and converted it to csv.")
        if (ref == TRUE) 
            reflist_gw <- c()
        names_gw <- c()
        for (i in 1:ngw) {
            message(paste0("Fetching food web ", i, " in ", ngw, 
                "!"))
            dfgw <- read.csv(paste0(folder, "/", files_gw[i]), 
                header = FALSE)
            dfgw <- dfgw[, colSums(is.na(dfgw)) <= 1]
            names_gw[i] <- as.character(dfgw[2, 1])
            if (ref == TRUE) 
                reflist_gw[i] <- as.character(dfgw[1, 1])
            names_gw_c <- c()
            n1 <- ncol(dfgw) - 1
            for (j in 1:n1) {
                names_gw_c[j] <- as.character(dfgw[2, j + 1])
            }
            names_gw_r <- c()
            n2 <- nrow(dfgw) - 2
            for (j in 1:n2) {
                names_gw_r[j] <- as.character(dfgw[j + 2, 1])
            }
            dfgw <- dfgw[-c(1, 2), -1]
            dfgw[dfgw == ""] <- NA
            dfgw <- na.omit(dfgw)
            if (i == 281) {
                names_gw_r <- names_gw_r[-c(36, 37)]
            }
            names_gw_c <- names_gw_c[names_gw_c != ""]
            names_gw_r <- names_gw_r[names_gw_r != ""]
            names_gw_c <- paste0("sp_", as.character(1:length(names_gw_c)), 
                "_", names_gw_c)
            names_gw_r <- paste0("sp_", as.character(1:length(names_gw_r)), 
                "_", names_gw_r)
            colnames(dfgw) <- names_gw_c
            rownames(dfgw) <- names_gw_r
            fwlist[[i]] <- dfgw
        }
        names(fwlist) <- names_gw
        if (ref == TRUE) {
            references <- as.data.frame(matrix(ncol = 4))
            names(references) <- c("FW code", "first_author", 
                "year", "full_ref")
            files_gw <- list.files(folder, pattern = "WEB")
            message("Fetching references from the dataset files!")
            for (w in 1:ngw) {
                dfgw <- read.csv(paste0(folder, "/", files_gw[w]), 
                  header = FALSE)
                dfgw <- dfgw[, colSums(is.na(dfgw)) <= 1]
                full_ref1 <- as.character(dfgw[1, 1])
                references[w, 4] <- full_ref1
                references[w, 1] <- files_gw[w]
                references[w, 2] <- str_sub(word(full_ref1, start = 1), 
                  1, str_length(word(full_ref1, start = 1)) - 
                    1)
                references[w, 3] <- regmatches(x = full_ref1, 
                  gregexpr("[0-9]+", text = full_ref1))[[1]][1]
            }
        }
        if (ecosyst == TRUE) {
            message("Searching for 'gw_list.csv' file...")
            if (!file.exists(paste0(folder, "/gw_list.csv"))) 
                stop("\nDownload the file 'Current Food Web List' from the website\n                                                             \nand convert to a csv named 'gw_list.csv' please!")
            gw_eco <- read.csv(paste0(folder, "/", "gw_list.csv"), 
                header = TRUE, sep = ";")
            filn <- paste0("WEB", as.character(gw_eco[, 1]), 
                ".csv")
            gw_eco2 <- gw_eco[, 1:3]
            gw_eco2[, 1] <- filn
            names(gw_eco2)[1] <- "FW"
            filn <- as.data.frame(cbind(filn, filn))
            names(filn) <- c("filn1", "filn2")
            ecosystem <- merge(x = filn, y = gw_eco2, by.x = "filn2", 
                by.y = "FW")
            ecosystem <- ecosystem[, c(2, 3, 4)]
            names(ecosystem)[1] <- "Food web"
        }
    }
    if (db == "wl") {
        message("####################### WEB OF LIFE DATABASE #######################\n\n")
        files_wl <- list.files(path = folder, pattern = ".csv")
        files_wl <- files_wl[files_wl != "references.csv"]
        nwl <- length(files_wl)
        message(paste0("There are ", nwl, " food web files in the folder!"))
        if (file.exists(paste0(folder, "/references.csv"))) {
            table_wl <- read.csv(paste0(folder, "/references.csv"), 
                header = TRUE)
        }
        else {
            stop("There is no 'references.csv' file on the folder, as provided by the website!")
        }
        names_wl <- as.character(table_wl[, 8])
        for (i in 1:nwl) {
            message(paste0("Fetching food web ", i, " in ", nwl, 
                "!"))
            dfwl <- read.csv(paste0(folder, "/", files_wl[i]), 
                header = TRUE, row.names = 1)
            dfwl[is.na(dfwl)] <- 0
            fwlist[[i]] <- dfwl
        }
        names(fwlist) <- names_wl
        if (ref == TRUE) {
            references <- as.data.frame(matrix(ncol = 4))
            names(references) <- c("FW code", "first_author", 
                "year", "full_ref")
            message("Fetching references from the 'references.csv' file!")
            message("Checking the presence of the 'references.csv' file...")
            if (!file.exists(paste0(folder, "/references.csv")) == 
                TRUE) 
                stop("Can't retrieve reference details... \n File not present!")
            ref_file <- read.csv(paste0(folder, "/references.csv"), 
                header = TRUE)
            for (w in 1:nwl) {
                full_ref1 <- as.character(ref_file[w, 7])
                references[w, 4] <- full_ref1
                references[w, 1] <- as.character(ref_file[w, 
                  1])
                references[w, 2] <- stringr::str_sub(stringr::word(full_ref1, 
                  start = 1), 1, stringr::str_length(stringr::word(full_ref1, 
                  start = 1)) - 1)
                references[w, 3] <- regmatches(x = full_ref1, 
                  gregexpr("[0-9]+", text = full_ref1))[[1]][1]
            }
        }
        if (spatial == TRUE) {
            message("Fetching the spatial information from the 'references.csv' file!")
            message("Checking the presence of the 'references.csv' file...")
            if (!file.exists(paste0(folder, "/references.csv")) == 
                TRUE) 
                stop("Can't retrieve spatial info... \n File not present!")
            ref_file <- read.csv(paste0(folder, "/references.csv"), 
                header = TRUE)
            spatial1 <- ref_file[, c(1, 9, 10)]
        }
    }
    if (db == "eb") {
        message("####################### ECOBASE DATABASE #######################\n\n")
        message("Fetching info from the EcoBase website!")
        suppressWarnings({
            suppressMessages({
                h = basicTextGatherer()
                curlPerform(url = "http://sirs.agrocampus-ouest.fr/EcoBase/php/webser/soap-client_3.php", 
                  writefunction = h$update)
                data1 <- xmlTreeParse(h$value(), useInternalNodes = TRUE)
                liste_mod <- ldply(xmlToList(data1), data.frame)
            })
            l2 <- subset(liste_mod, model.dissemination_allow == 
                "true")
            message("Sellected only those to which model dissemination is allowed!")
            l3 <- subset(l2, model.whole_food_web == "true")
            message("Sellected only those to which the whole food web is available!")
            model.name <- as.character(l3$model.model_name)
            input_list <- list()
            id <- as.numeric(as.character(l3$model.model_number))
            for (i in 1:nrow(l3)) {
                message(paste0("Fetching information on food web ", 
                  i, " of ", nrow(l3)))
                suppressMessages({
                  h = basicTextGatherer()
                  mymodel <- id[i]
                  curlPerform(url = paste("http://sirs.agrocampus-ouest.fr/EcoBase/php/webser/soap-client.php?no_model=", 
                    mymodel, sep = ""), writefunction = h$update, 
                    verbose = TRUE)
                  data2 <- xmlTreeParse(h$value(), useInternalNodes = TRUE)
                  input1 <- xpathSApply(data2, "//group", function(x) xmlToList(x))
                })
                names_input <- as.character(input1[1, ])
                input1 <- as.data.frame(input1)
                colnames(input1) <- names_input
                input1 <- input1[-1, ]
                input_list[[i]] <- input1
            }
            mnames <- names(input_list)
            for (i in 1:length(input_list)) {
                m2 <- input_list[[i]]
                nnodes <- length(m2)
                node_names <- names(m2)
                int_matrix <- as.data.frame(matrix(ncol = nnodes, 
                  nrow = nnodes))
                for (j in 1:length(m2)) {
                  node1 <- m2[[j]]
                  node_id <- as.numeric(node1$group_seq)
                  node_name <- node_names[j]
                  colnames(int_matrix)[node_id] <- node_name
                  rownames(int_matrix)[node_id] <- node_name
                  diet_node1 <- node1$diet_descr
                  nr_food_items <- length(diet_node1)
                  for (a in 1:nr_food_items) {
                    item1 <- diet_node1[[a]]
                    id_item1 <- as.numeric(item1$prey_seq)
                    proportion_item1 <- as.numeric(item1$proportion)
                    detritus_item1 <- as.numeric(item1$detritus_fate)
                    int_matrix[id_item1, node_id] <- proportion_item1
                  }
                }
                int_matrix[is.na(int_matrix)] <- 0
                fwlist[[i]] <- int_matrix
            }
            names(fwlist) <- model.name
        })
        if (ref == TRUE) {
            references <- as.data.frame(matrix(ncol = 4))
            names(references) <- c("FW code", "first_author", 
                "year", "full_ref")
            message("Fetching the references information!")
            for (w in 1:nrow(l3)) {
                full_ref1 <- as.character(l3$model.reference)[w]
                references[w, 4] <- full_ref1
                references[w, 1] <- as.numeric(as.character(l3$model.model_number[w]))
                references[w, 2] <- as.character(l3$model.author[w])
                references[w, 3] <- regmatches(x = full_ref1, 
                  gregexpr("[0-9]+", text = full_ref1))[[1]][1]
            }
        }
        if (ecosyst == TRUE) {
            ecosystem <- data.frame(l3$model.model_number, l3$model.country, 
                l3$model.ecosystem_type)
            names(ecosystem) <- c("Food web", "Location", "Ecosystem")
        }
        if (spatial == TRUE) {
            message("Fetching spatial information from the EcoBase website...")
            if (!file.exists("ecobase_areas.shp")) {
                stop("If you need the spatial information on each dataset you have to:\n\n             1. Download the kml file from http://sirs.agrocampus-ouest.fr/EcoBase/php/protect/extract_kml.php;\n\n             (file name is 'location.kml')\n\n             2. Convert it to a shapefile in any GIS;\n\n             3. Name it 'ecobase_areas.shp';\n\n             4. Place it in the working directory;\n\n             ... I know, it is not ideal!...\n             ")
            }
            else EcoBase_shape <- sf::st_read("ecobase_areas.shp")
            ebd <- EcoBase_shape$Name
            nmr <- list()
            for (i in 1:length(ebd)) {
                nr <- strsplit(as.character(ebd[i]), "--::")[[1]][1]
                nr <- as.numeric(str_extract_all(nr, "\\d+")[[1]])
                nmr[[i]] <- nr
            }
            nmr2 <- c()
            for (i in 1:length(nmr)) {
                a <- nmr[[i]]
                b <- length(a)
                c1 <- rep(i, b)
                nmr2 <- c(nmr2, c1)
            }
            nmr <- unlist(nmr)
            table1 <- as.data.frame(cbind(nmr2, nmr))
            colnames(table1) <- c("row_n", "id")
            lines_n <- c()
            for (i in 1:nrow(liste_mod)) {
                id <- as.numeric(as.character(liste_mod$model.model_number[i]))
                lines_n[i] <- as.numeric(table1[table1$id == 
                  id, ][1])
            }
            ecobase_poly2 <- list()
            for (i in 1:length(lines_n)) {
                ecobase_poly2[i] <- st_geometry(EcoBase_shape)[lines_n[i]]
            }
            for (i in 1:length(ecobase_poly2)) {
                if (is.na(lines_n[i])) {
                  z1 <- as.numeric(unlist(regmatches(liste_mod$model.geographic_extent[[i]], 
                    gregexpr("[[:digit:]]+\\.*[[:digit:]]*", 
                      liste_mod$model.geographic_extent[[i]]))))
                  z2 <- c(z1[4], z1[1], z1[2], z1[1], z1[2], 
                    z1[3], z1[4], z1[3])
                  x1 <- as.data.frame(matrix(z2, ncol = 2, byrow = TRUE))
                  x1 <- cbind(x1[2], x1[1])
                  p1 <- Polygon(x1)
                  ps1 <- Polygons(list(p1), 1)
                  ecobase_poly2[[i]] <- st_as_sf(SpatialPolygons(list(ps1)))
                }
                ecobase_poly2[[i]] <- ecobase_poly2[[i]]
            }
            for (i in 1:length(ecobase_poly2)) {
                if (!any(class(ecobase_poly2[[i]]) == "sf")) {
                  t2 <- ecobase_poly2[[i]]
                  t3 <- st_cast(t2, to = "POLYGON")
                  ecobase_poly2[[i]] <- st_as_sf(as(st_zm(st_geometry(t3)), 
                    "Spatial"))
                }
                else message("Ok!")
            }
            table2 <- as.data.frame(cbind(1:length(ecobase_poly2), 
                as.numeric(as.character(liste_mod$model.model_number))))
            names(table2) <- c("row", "id")
            id_selected <- as.numeric(as.character(l3$model.model_number))
            rows_selected <- c()
            for (i in 1:length(id_selected)) {
                rows_selected[i] <- as.numeric(table2[table2["id"] == 
                  id_selected[i], ][1])
            }
            spatial1 <- ecobase_poly2[rows_selected]
        }
    }
    if (db == "mg") {
        message("####################### MANGAL DATABASE #######################\n\n")
        message("Fetching datasets from the Mangal website! \nThis operation might take a long time!")
        if (is.null(mangal_types)) 
            mangal_types <- c("predation", "herbivory")
        if ("all" %in% mangal_types) {
            mangal_types <- c("competition", "predation", "herbivory", 
                "amensalism", "neutralism", "commensalism", "mutualism", 
                "parasitism", "symbiosis", "scavenger", "detritivore")
            message("You are downloading the all types of interactions in the mangal database:\n              competition, predation, herbivory, amensalism, neutralism, commensalism,\n              mutualism, parasitism, symbiosis, scavenger, detritivore")
        }
        else mangal_types <- mangal_types
        ntypes <- length(mangal_types)
        net_info <- list()
        type_info <- c()
        for (i in 1:ntypes) {
            message(paste0("\n\nFetching information from interactions of the type ", 
                "'", mangal_types[i], "'!"))
            df_inter <- search_interactions(type = mangal_types[i], 
                verbose = TRUE)
            if (nrow(df_inter) > 0) 
                fwlist1 <- get_collection(df_inter, verbose = TRUE)
            if (nrow(df_inter) > 0) 
                net_info <- c(net_info, fwlist1)
            if (nrow(df_inter) > 0) 
                fwlist2 <- rmangal::as.igraph(fwlist1)
            if (nrow(df_inter) > 0) 
                type_info <- c(type_info, rep(mangal_types[i], 
                  length(fwlist2)))
            if (nrow(df_inter) > 0) 
                fwlist <- c(fwlist, fwlist2)
        }
        for (i in 1:length(fwlist)) {
            fw2 <- fwlist[[i]]
            fw3 <- igraph::as_data_frame(fw2, what = "both")
            id_name <- fw3$vertices[, 1:2]
            for (j in 1:nrow(id_name)) {
                node_name <- (paste0(id_name$original_name[j], 
                  "_", id_name$name[j]))
                if (grepl(":", node_name, fixed = TRUE)) {
                  node_name <- tail(strsplit(node_name, ": "))[[1]]
                  id_name[j, 2] <- node_name[2]
                }
                else id_name[j, 2] <- node_name
            }
            id_edges <- fw3$edges[, 1:3]
            int_matrix <- as.data.frame(matrix(ncol = nrow(id_name), 
                nrow = nrow(id_name)))
            colnames(int_matrix) <- id_name$original_name
            rownames(int_matrix) <- id_name$original_name
            for (a in 1:nrow(id_edges)) {
                edge1 <- as.numeric(id_edges[a, 1:2])
                name1 <- id_name[as.character(edge1[1]), ][, 
                  2]
                name2 <- id_name[as.character(edge1[2]), ][, 
                  2]
                int_matrix[name1, name2] <- 1
            }
            int_matrix[is.na(int_matrix)] <- 0
            fwlist[[i]] <- int_matrix
        }
        references <- as.data.frame(matrix(ncol = 6))
        names(references) <- c("Dataset ID", "Type of interaction", 
            "Original ID", "first_author", "year", "DOI")
        message("Fetching references!")
        for (j in 1:length(net_info)) {
            dataset_id <- net_info[[j]]$dataset$dataset_id
            first_author <- net_info[[j]]$reference$first_author
            year_mng <- as.numeric(net_info[[j]]$reference$year)
            doi_mng <- net_info[[j]]$reference$doi
            references[j, 3] <- dataset_id
            references[j, 4] <- first_author
            references[j, 5] <- year_mng
            references[j, 6] <- doi_mng
            references <- references[order(references$`Dataset ID`), 
                ]
            rownames(references) <- 1:nrow(references)
        }
        references[, 1] <- paste0("mg_", 1:nrow(references))
        references[, 2] <- type_info
        names(fwlist) <- paste0("mg_", references[, 1])
        if (spatial == TRUE) {
            spatial1 <- as.data.frame(matrix(ncol = 4))
            names(spatial1) <- c("Dataset ID", "first_author", 
                "lat", "long")
            message("Fetching coordinates!")
            for (z in 1:length(net_info)) {
                dataset_id <- net_info[[z]]$dataset$dataset_id
                lat_mng <- net_info[[z]]$network$geom_lat
                long_mng <- net_info[[z]]$network$geom_lon
                first_author <- net_info[[z]]$reference$first_author
                if (length(unlist(lat_mng)) > 1) {
                  spatial2 <- as.data.frame(matrix(ncol = 4))
                  names(spatial2) <- c("Dataset ID", "first_author", 
                    "long", "lat")
                  for (b in 1:length(unlist(lat_mng))) {
                    spatial2[b, 3] <- long_mng[[1]][b]
                    spatial2[b, 4] <- lat_mng[[1]][b]
                  }
                  spatial2[, 1] <- dataset_id
                  spatial2[, 2] <- first_author
                  spatial1 <- rbind(spatial1, spatial2)
                }
                spatial1[z, 1] <- dataset_id
                spatial1[z, 2] <- first_author
                if (length(unlist(lat_mng)) == 1) 
                  spatial1[z, 3] <- lat_mng
                if (length(unlist(lat_mng)) == 1) 
                  spatial1[z, 4] <- long_mng
            }
            spatial1 <- spatial1[order(spatial1$`Dataset ID`), 
                ]
            rownames(spatial1) <- 1:nrow(spatial1)
        }
    }
    message(paste0("DONE! \n\nOverall the list stores ", length(fwlist), 
        " datasets!"))
    master_list <- list()
    master_list[["int_matrix"]] <- fwlist
    if (ecosyst == TRUE) {
        master_list[["ecosystem"]] <- ecosystem
        message("\n Additional element in the results: \n\n The vector with information on the ecosystems.")
    }
    if (ref == TRUE) {
        master_list[["references"]] <- references
        message("Additional element in the results! \nA data frame with information on the references.")
    }
    if (spatial == TRUE) {
        master_list[["spatial_info"]] <- spatial1
        message("\n Additional element in the results: \n\n Spatial information was added.")
    }
    if (code == TRUE) {
        if (db == "gw") 
            master_list[["code"]] <- files_gw
        if (db == "wl") 
            master_list[["code"]] <- files_wl
        if (db == "mg") 
            master_list[["code"]] <- references[, 1]
        message("Added food web code information.")
    }
    if (length(master_list) == 1) 
        return(fwlist)
    if (length(master_list) != 1) 
        return(master_list)
    message("####################### DONE! #######################")
}

robustness<-function (fw_to_attack, probs_of_fw, alpha1){
	basals<-which(degree(fw_to_attack,mode="in") == 0)
    isolates <- function(g) {
        return(setdiff(which(degree(g,mode="in") == 0),basals))
    }
    fw_nodes <- V(fw_to_attack)$name
    n_species <- length(fw_nodes)
    i_output_list <- list()
    for (j in 1:ncol(probs_of_fw)) {
        output_nodes_and_links <- data.frame(matrix(ncol = n_species, nrow = 5))
        colnames(output_nodes_and_links) <- paste0("del_species_", 1:(n_species - 1))
        rownames(output_nodes_and_links) <- c("nodes", "links", "secondary_extinctions", "%_extinctions", "n_primary_extinctions")
        probs_i <- probs_of_fw[, j]
        n_links_original <- gsize(fw_to_attack)
        perc_ext <- 0
        for (z in 1:(n_species-1)) {
            node_to_kill <- sample(x = fw_nodes, size = z, replace = FALSE, prob = probs_i)
            fw_resulting_from_attack <- delete_vertices(fw_to_attack, node_to_kill)
            secondary_extinctions <- isolates(fw_resulting_from_attack)
			nb_sec_ext<-length(secondary_extinctions)
			while(length(secondary_extinctions)>0){
				fw_resulting_from_attack <- delete_vertices(fw_resulting_from_attack, secondary_extinctions)
				secondary_extinctions <- isolates(fw_resulting_from_attack)
				nb_sec_ext<-nb_sec_ext+length(secondary_extinctions)
			}
            if (gorder(fw_resulting_from_attack) == 0) {
                output_nodes_and_links[1, z] <- 0
                output_nodes_and_links[2, z] <- 0
                output_nodes_and_links[3, z] <- z-n_species
                output_nodes_and_links[4, z] <- 100
                output_nodes_and_links[5, z] <- z
            }
            if (gorder(fw_resulting_from_attack) != 0) {
                nodes_in_original_fw <- n_species
                nodes_in_fw_resulting_from_attack <- gorder(fw_resulting_from_attack)
                lost_nodes <- nodes_in_original_fw - nodes_in_fw_resulting_from_attack
                number_of_secondary_extinctions <- nb_sec_ext
                links_in_original_fw <- n_links_original
                links_in_fw_resulting_from_attack <- gsize(fw_resulting_from_attack)
                lost_links <- links_in_original_fw - links_in_fw_resulting_from_attack
                perc_ext <- (lost_nodes * 100)/n_species
                output_nodes_and_links[1, z] <- nodes_in_fw_resulting_from_attack
                output_nodes_and_links[2, z] <- links_in_fw_resulting_from_attack
                output_nodes_and_links[3, z] <- number_of_secondary_extinctions
                output_nodes_and_links[4, z] <- perc_ext
                output_nodes_and_links[5, z] <- z
            }
        }
        i_output_list[[j]] <- output_nodes_and_links
    }
    R_alpha1 <- NA
    for (x in 1:length(i_output_list)) {
        df1 <- i_output_list[[x]]
        df1[4, ] <- round(as.numeric(df1[4, ]))
        if (any(as.numeric(df1[4, ]) <= alpha1, na.rm = TRUE)) {
            col1 <- max(which(df1[4, ] <= alpha1))
            R_alpha1[x] <- df1[5, col1]/n_species
        }
        else {
            R_alpha1[x] <- 0
        }
    }
    return(list(Simulation_results = i_output_list, Ralpha = R_alpha1))
}

fw.metrics <- function(list1){
  #all_models_01


  #Check the list1 structure
  if(class(list1[[1]])=="list") {
    list1 <- list1[[1]]
    }

  #dir.create(folder_name)
  #message(paste0("Just created a folder named ", folder_name, " to save all the intermediate files..."))
  #redefine wd
  #previous_WD <- getwd()
  #setwd(paste0(previous_WD,paste0("/", folder_name)))
  #mnames1 <- names(FWlist)
  nnodes <- c()
  nlinks <- c()
  linkdens <- c()
  connectance <- c()
  compartmentalization <- c()
  max_tlevel <- c()

  #nrFW <- length(FWlist)
  #if (plotFW==TRUE) par(mfrow3d(nr=2, nc=round(nrFW/2)))

  for(i in 1:length(list1)){
    message(paste0("Computing network metrics for food web ", i, " of ", length(list1), "..."))
    #fw1 <- all_models_01[[i]]
    tl <- list1[[i]]
    if(!any(apply(tl, 2, function(x) is.numeric(x)))) tl <- apply(tl, 2, function(x) as.numeric(x))
    test1 <- NetIndices::GenInd(tl)
    nnodes <- c(nnodes,test1$N)#number of nodes
    nlinks <- c(nlinks,test1$Ltot)#number of links
    linkdens <- c(linkdens,test1$LD)#link density (average # of links per node)
    connectance <- c(connectance,test1$C)#the connectance of the graph
    compartmentalization <- c(compartmentalization,test1$Cbar)#compartmentalization [0,1]
    test2 <- NetIndices::TrophInd(tl)
    max_tlevel <- c(max_tlevel,max(test2$TL))

    #nnodes[i] <- test1$N#number of nodes
    #nlinks[i] <- test1$Ltot#number of links
    #linkdens[i] <- test1$LD#link density (average # of links per node)
    #connectance[i] <- test1$C#the connectance of the graph
    #compartmentalization[i] <- test1$Cbar#compartmentalization [0,1]
    #test2 <- TrophInd(tl)
    #max_tlevel[i] <- max(test2$TL)

    #write.table(tl, file = paste0("fw_",i ,".csv"), append=FALSE, sep=",", col.names=FALSE, row.names=FALSE)
    #analyse.single(filename=paste0("fw_",i ,".csv"))
    #tl_table <- read.csv(file=paste0("Results-", "fw_",i ,".csv"), header=TRUE, sep=",")
    #tl_tlevels <- tl_table$Total...trophic.positions
    #tlevels[i] <- tl_tlevels
    #connectance[i] <- tl_table$Connectance
    #if (plotFW==TRUE){
    #color <- heat.colors(tl_tlevels)
    #radii <- rep(5,tl_tlevels)
    #plotweb(cols=color, radii=radii)
    #title3d(main=mnames1[i])
    #}
  }


  result <- list(number_nodes=nnodes,
                 number_links=nlinks,
                 link_density=linkdens,
                 connectance=connectance,
                 compartmentalization=compartmentalization,
                 maximum_trophic_level=max_tlevel
                 )

  #setwd(previous_WD) #restore wd

  #rgl.snapshot(filename="FW.png", fmt = "png", top = TRUE)

  return(result)

}
