setwd("C:\\Massol\\Enseignement\\Formation réseaux\\Formation EcoNet 2024")
rm(list=ls())

# Special installs (unhide if needed; also, check Rtools installation if issues appear)
#devtools::install_github("FMestre1/fw_package")

# if the install of FWebs fails (can happen with Macs), install rmangal and use the following lines for the extraction of the dataset
# library(rmangal)
# mg1 <- create.fw.list(db="mg", ref=TRUE, spatial = TRUE)
# and source('crutch_functions.R') to get the useful functions from the package

# Loading functions
source('functions.R')

## Loading data

#food web from Cruz-Escalona, V. H., Arreguín-Sánchez, F. & Zetina-Rejón, M. (2007) Analysis of the ecosystem structure of Laguna Alvarado, western Gulf of Mexico, by means of a mass balance model. Estuarine, Coastal and Shelf Science, 72, 155-167.

mat_foodweb<-t(as.matrix(mg1[[1]][[223]]))
rownames(mat_foodweb)<-names(mg1[[1]][[223]])
colnames(mat_foodweb)<-names(mg1[[1]][[223]])

#plant-pollinator web from Barrett, S. C. H. & Helenurm, K. (1987) The reproductive biology of boreal forest herbs. I. Breeding systems and pollination. Canadian Journal of Botany, 65, 2036-2046.

mat_plantpol<-barrett1987
mat_plantpol_bin<-mat_plantpol
mat_plantpol_bin[mat_plantpol>0]<-1

## Building graphs and first plots

foodweb<-graph_from_adjacency_matrix(mat_foodweb)
plot(foodweb,layout=layout_as_food_web3(foodweb))
plotMyMatrix(as_adj(foodweb,sparse=FALSE))

undirected_foodweb<-as.undirected(foodweb)
plotMyMatrix(as_adj(undirected_foodweb,sparse=FALSE))

pollination<-graph_from_biadjacency_matrix(mat_plantpol)
plot(pollination,layout=layout_as_bipartite)
plotMyMatrix(as_adj(pollination,sparse=FALSE))
plotMyMatrix(as_biadjacency_matrix(pollination,sparse=FALSE))

pollination_bin<-graph_from_biadjacency_matrix(mat_plantpol_bin)

plotweb(mat_plantpol)

##### Advanced metrics
# first, have a look at automatic outputs from Fwebs
fw.metrics(list(list(mat_foodweb)))
# and from bipartite
networklevel(mat_plantpol)

#### degrees, etc.
degree(foodweb)
degree(foodweb,mode="in")
degree(foodweb,mode="out")

###Plot degree distribution
hist(degree(foodweb),breaks=0:max(degree(foodweb)))
plot(degree_distribution(foodweb, cumulative = TRUE),type="l")
dd.fw(list(as.data.frame(mat_foodweb)), log = FALSE, cumulative = TRUE)

###Comparison of degree distribution
ks.test(degree(foodweb),"pbinom",size=length(V(foodweb)),prob=mean(degree(foodweb))/length(V(foodweb)))

ks.test(degree(foodweb),"ppois",lambda=mean(degree(foodweb)))

ks.test(degree(foodweb),"pnbinom",mu = mean(degree(foodweb)), size = mean(degree(foodweb))^2/(var(degree(foodweb))-mean(degree(foodweb))))

#### Compute the connectance of the empirical network
mean(mat_foodweb)
DirectedConnectance(as_Community(foodweb)) 
mean(as_adj(undirected_foodweb,sparse=FALSE))/2
mean(as_adj(foodweb,sparse=FALSE))
fw.metrics(list(list(mat_foodweb)))$connectance

#### trophic levels
### classic measures
foodweb_TL<-TrophicLevels(as_Community(foodweb))

plotMyMatrix(mat_foodweb,clustering=list("row"=foodweb_TL[,1],"col"=foodweb_TL[,1]))
plotMyMatrix(mat_foodweb,clustering=list("row"=foodweb_TL[,3],"col"=foodweb_TL[,3]))


### MacKay et al.'s method
count_components(foodweb)
tl.1<-trophic_levels(largest_component(foodweb))

plot(TrophicLevels(as_Community(largest_component(foodweb),"."))[,1],tl.1[,1],xlab="ShortestTL",ylab="MacKayTL")
plot(TrophicLevels(as_Community(largest_component(foodweb),"."))[,6],tl.1[,1],xlab="PreyAveragedTL",ylab="MacKayTL")

#### modularity & clustering
### modularity
foodweb_EB.mod<-cluster_edge_betweenness(undirected_foodweb)
foodweb_LE.mod<-cluster_leading_eigen(undirected_foodweb)
foodweb_ML.mod<-cluster_louvain(undirected_foodweb)

par(mfrow=c(1,3))
plot(foodweb_EB.mod,foodweb,layout = layout_as_food_web(foodweb))
plot(foodweb_LE.mod,foodweb,layout = layout_as_food_web(foodweb))
plot(foodweb_ML.mod,foodweb,layout = layout_as_food_web(foodweb))

plotMyMatrix(as_adj(undirected_foodweb,sparse=FALSE),clustering=list("row"=foodweb_ML.mod$membership,"col"=foodweb_ML.mod$membership))


make_alluvial_2(foodweb_ML.mod$membership,foodweb_LE.mod$membership,"Louvain","Leading_eigen")
make_alluvial_2(foodweb_ML.mod$membership,foodweb_EB.mod$membership,"Louvain","Edge_betweenness")

pollination_LE.mod<-cluster_leading_eigen(pollination_bin)

plotMyMatrix(mat_plantpol_bin,clustering=list("row"=pollination_LE.mod$membership[!V(pollination_bin)$type],"col"=pollination_LE.mod$membership[V(pollination_bin)$type]))


### spectral clustering
#plot(4:15,sapply(4:15,function(k) modularity(undirected_foodweb,spectral_clustering(undirected_foodweb,k))),type="l",ylab="modularity",xlab="nb of clusters")

foodweb_SG<-laplacian_spectral_gap(undirected_foodweb)
foodweb_SG$optim_n

foodweb_SC<-spectral_clustering(undirected_foodweb,5)
plotMyMatrix(as_adj(undirected_foodweb,sparse=FALSE),clustering=list("row"=foodweb_SC,"col"=foodweb_SC))

modularity(undirected_foodweb,foodweb_SC)

make_alluvial_2(foodweb_ML.mod$membership,foodweb_SC,"Louvain","Spectral clustering")

foodweb_SC<-spectral_clustering(undirected_foodweb,9)
plotMyMatrix(as_adj(undirected_foodweb,sparse=FALSE),clustering=list("row"=foodweb_SC,"col"=foodweb_SC))

modularity(undirected_foodweb,foodweb_SC)


#### generalism, network specialization, nestedness

### node specialization/generalism from Blüthgen's index
dfun(mat_plantpol)
plot(degree(pollination)[!V(pollination_bin)$type],dfun(mat_plantpol)$dprime,xlab="degrees",ylab="d'")

dfun(t(mat_plantpol))
plot(degree(pollination)[V(pollination_bin)$type],dfun(t(mat_plantpol))$dprime,xlab="degrees",ylab="d'")

foodweb_spe.res<-dfun(mat_foodweb)$dprime #as resource
foodweb_spe.con<-dfun(t(mat_foodweb))$dprime #as consumer
interm_species_list<-intersect(names(foodweb_spe.res),names(foodweb_spe.con))
plot(foodweb_spe.res[which(names(foodweb_spe.res)%in%interm_species_list)],foodweb_spe.con[which(names(foodweb_spe.con)%in%interm_species_list)],xlab="d' as prey",ylab="d' as consumer")

### network specialization
H2fun(mat_plantpol)

### nestedness
pollination_nestdness<-nested(mat_plantpol, method = "ALL", rescale=TRUE, normalised=TRUE)
nestednodf(mat_plantpol)
nestednodf(mat_plantpol,weighted=TRUE)
nestednodf(mat_plantpol,weighted=TRUE,wbinary=T)
nestednodf(mat_plantpol_bin)
nestednodf(mat_plantpol_bin,weighted=TRUE)
nestednodf(mat_plantpol_bin,weighted=TRUE,wbinary=T)

#### robustness to species removal
niche<-niche_matrix(0.2,200)
m<-niche$matrix
net<-graph_from_adjacency_matrix(m,mode="directed")

i_index <- seq(from = 0, to = 0.95, by =0.05)
prob_exp<-exponent.removal(net, i_index)
V(net)$name<-1:200
iterate(fw_to_attack=net, prob_exp, alpha1=50, iter=10, i_index, plot = TRUE)

prob_exp<-exponent.removal(foodweb, i_index)
iterate(fw_to_attack=foodweb, prob_exp, alpha1=50, iter=20, i_index, plot = TRUE)

#### beta diversity of networks

gList <- c()
for(i in 1:4){
  graphLocal <- sample_gnp(60, 0.1, directed=TRUE)
  V(graphLocal)$name <- as.character(1:60)
  gList <- c(gList, list(graphLocal))
}
names(gList) <- c("A","B","C","D")

disPairwise(gList, type='P')
disPairwise(gList, type='L')
disPairwise(gList, type='Pi')





##### Null models

#### configuration models, degree sequences
### randomize unipartite network from degree sequence (Viger-Latapy's method)
net<-sample_gnp(50,0.2, directed=FALSE)
sample.config.undirected<-lapply(1:100,function(x) sample_degseq(degree(net), method = "vl"))
length(sample.config.undirected)

alt.config<-config_VL(net,100)
plot(alt.config[[42]])

one_comp_foodweb<-as.undirected(largest_component(foodweb))
one_comp_foodweb_LE.mod<-cluster_leading_eigen(one_comp_foodweb)
one_comp_foodweb_LE.mod$mod

foodweb_configs<-config_VL(one_comp_foodweb,1000)
mods_configs<-sapply(1:1000, function(x) cluster_leading_eigen(foodweb_configs[[x]])$mod)
p.val(test_val=one_comp_foodweb_LE.mod$mod,test_collection=mods_configs,method="larger",label="modularity")


### randomize unipartite directed networks
net<-sample_gnp(50,0.2, directed =FALSE)
net_directed<-make_food_web_from_undirected(net,5)
sample.config.directed<-lapply(1:100,function(x) sample_degseq(degree(net_directed,mode="out"), degree(net_directed,mode="in"), method = "simple.no.multiple"))

par(mfrow=c(1,2))
plot(net_directed,layout=layout_as_food_web3(net_directed))
plot(sample.config.directed[[1]],layout=layout_as_food_web3(sample.config.directed[[1]]))


### randomize bipartite network (Strona's curveball algorithm)
net<-sample_bipartite(40,60,"gnp",0.1)
net<-largest_component(net)
net_mat<-as.matrix(as_biadjacency_matrix(net))
sample.bip.config<-simulate(vegan::nullmodel(net_mat,"curveball"),nsim=1000) 
dim(sample.bip.config)

alt.config<-config_VL(net,1000)

net_nestedness<-nested(net_mat, method = "NODF2")
nestedness_configs<-sapply(1:1000, function(x) nested(sample.bip.config[,,x], method = "NODF2"))

p.val(net_nestedness,nestedness_configs,method="two-sided",label="nestedness")



##### de novo generative models

#### generate unipartite food webs

### generate random directed unipartite network using Erdos-Renyi model
net<-make_food_web_from_undirected(sample_gnp(50,0.2, directed =TRUE),basal = 10)
V(net)$name<-sapply(1:50,function(x) paste0("sp_",x))
plot(net,layout=layout_as_food_web2(net))
#plot(net,layout=layout_as_food_web(net))

ks.test(degree(net),"pbinom",length(V(net))-1,mean(degree(net))/(length(V(net))-1))

### generate random food web using preferential attachment algorithm
net<-make_food_web_from_undirected(sample_pa(500, power = 1, directed = FALSE, out.pref=TRUE),basal = 50)
plot(net,layout=layout_as_food_web2(net))

net_dist<-displ$new(degree(net))
net_dist$setXmin(estimate_xmin(displ$new(degree(net)))$xmin)
net_pars<-estimate_pars(net_dist)

ks.test(degree(as.undirected(net)),"ppldis",xmin = estimate_xmin(displ$new(degree(net)))$xmin, alpha = net_pars$pars)


### generate random food web according to the cascade model (Cohen-Newman-Briand)
net<-cascade_matrix(3,50)
sum(net)/(dim(net)[1]*(dim(net)[1]-1))

graph_cascade<-graph_from_adjacency_matrix(net)
V(graph_cascade)$name<-sapply(1:50,function(x) paste0("sp_",x))
plot(graph_cascade,layout=layout_as_food_web3(graph_cascade))

net<-cascade_matrix(3,200)
sum(net)/(dim(net)[1]*(dim(net)[1]-1))

### generate random food web according to the niche model (Williams-Martinez)
net<-niche_matrix(0.1,50)
sum(net$matrix)/(dim(net$matrix)[1]*(dim(net$matrix)[1]-1))

graph_niche<-graph_from_adjacency_matrix(net$matrix)
V(graph_niche)$name<-sapply(1:50,function(x) paste0("sp_",x))
plot(graph_niche,layout=layout_as_food_web3(graph_niche))

net<-niche_matrix(0.1,200)
sum(net$matrix)/(dim(net$matrix)[1]*(dim(net$matrix)[1]-1))


### generate food web with prescribed degree sequence (Dubart-Massol model) // deterministic model
net<-generate_DM_model(50,0.1,quant_fun="qpois", lambda=5)
plot(net,layout=layout_as_food_web3(net))

net<-generate_DM_model(50,0.1,quant_fun="qnbinom", mu = 4, size=50)
plot(net,layout=layout_as_food_web3(net))

net<-generate_DM_model(450,0.1,quant_fun="qpois", lambda=7)
hist(degree(net),breaks=0:max(degree(net)),main="")

ks.test(degree(net),"ppois",lambda = mean(degree(net)))


### generate a food web using the EDD model (expected degree distribution)
net_EDD<-Simul_EDD(50,0.2,2)
graph_EDD<-graph_from_adjacency_matrix(net_EDD$net,mode="undirected")
graph_EDD<-largest_component(graph_EDD)
plotMyMatrix(net_EDD$net)

foodweb_EDD<-make_food_web_from_undirected(graph_EDD,5)
plot(foodweb_EDD,layout=layout_as_food_web3(foodweb_EDD))


#### generate bipartite networks

### generate random bipartite network using Erdos-Renyi model
net<-sample_bipartite(25,25,"gnp",0.1)
plot(net,layout=layout_as_bipartite)
plotweb(as_biadjacency_matrix(net))

### generate random BEDD network (algo by Ouadah-Latouche-Robin)
net_bedd<-SimulB_EDD(25, 25, 0.1, 2, 2)
graph_bedd<-graph_from_biadjacency_matrix(net_bedd$net)
plot(graph_bedd,layout=layout_as_bipartite)
plotweb(net_bedd$net)
plotMyMatrix(net_bedd$net)


### randomize bipartite network, but only keeping expectations of degree (EDD model)

#example use with nestedness in bipartite networks
sample.bip.EDD<-lapply(1:1000, function(x) randomize.BEDD(net_mat))
nestedness_EDD<-sapply(1:1000, function(x) nested(sample.bip.EDD[[x]], method = "NODF2"))
p.val(net_nestedness,nestedness_EDD,method="two-sided",label="nestedness")

plot(density(nestedness_configs),xlim=c(min(nestedness_configs,nestedness_EDD),max(nestedness_configs,nestedness_EDD)),xlab="",main="nestedness distributions",col="blue")
lines(density(nestedness_EDD),col="darkgreen")

#example use with modularity in food webs
foodweb_EDD<-lapply(1:1000, function(x) randomize.EDD(one_comp_foodweb))
mods_EDD<-sapply(1:1000, function(x) cluster_leading_eigen(as.undirected(foodweb_EDD[[x]]))$mod)
p.val(one_comp_foodweb_LE.mod$mod,mods_EDD,method="larger",label="modularity")

plot(density(mods_configs),xlim=c(min(mods_configs,mods_EDD),max(mods_configs,mods_EDD)),xlab="",main="modularity distributions",col="blue")
lines(density(mods_EDD),col="darkgreen")






