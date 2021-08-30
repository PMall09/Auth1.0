#CODE 1:
usertype Timestamp,PUF,SK;  #SK : Secret Key
hashfunction H;
const XOR:Function;
const ADD:Function;
const MUL:Function;
const GEN:Function;
const  IDd, IDs, IDcs, SN, T, Kd, Aj, Bj, 
Tj, IDsj, Cj, L,N, Td, Tcs, Kd', RMd', 
RMd, L', P, U, Q, Q', SKes-d', RMj', Rj', 
Cd, Ed, Fd, LRj,LRj', RRj,RRj', Rd', SKs-d', Cd',V ;
const ADD:Function;
protocol Major1(Sensor, Drone, Cloud) #The code present the authentication procedure
                                      #between the Sensor node, Drone and the Cloud Server
{
role Sensor
{
const IDs;# Sensor node Identity
fresh RMj,Rj,SKs-d: Nonce;# RMj, Rj and SKs-d are the randomly chosen values
macro Aj =  H(IDsj, IDd, Rj, RMj, Tj);
macro Bj = XOR( RMj, H(IDsj, Rj, Tj));
send_!1(Sensor, Drone, IDsj, Aj, Bj, Tj); # sends the concatenated values to the Drone
recv_!4(Drone, Sensor, IDd, Cd, Ed, Fd); # receives the values from the Drone
macro Rd' = XOR(Fd, H(IDsj, LRj')); 
macro SKs-d' = XOR(Ed, H(IDsj, RRj'));
macro Cd' = H(IDd, IDsj, Rd', SKs-d');
match(Cd', Cd);  # if the values matches then the Drone is authenticated to the Sensor node 
claim(Sensor, Niagree); # Non-injective agreement
claim(Sensor, Nisynch); # Non-injective synchronization
claim(Sensor,Secret, SKs-d);# Checks whether the common key SKs-d is secret
}



role Drone{
const IDd;# Drone Identity
fresh RMd,SKes-d: Nonce; #RMd, sKes-d are the randomly chosen values
var RMj, Rj: Nonce;
recv_!1(Sensor, Drone, IDsj, Aj, Bj, Tj);# receives the values from the Sensor node
macro L = H(IDd, Kd, RMd, Td);
macro N = XOR(RMd, H(IDcs, Kd));
send_!2(Drone, Cloud, IDd, L, N, Td); # sends the values to the Cloud
recv_!3(Cloud, Drone, P, Q, V, Tcs);# receives the values from the Cloud
macro SKes-d' = XOR(V, H(IDd, Kd, Tcs)); 
macro Rcs' = XOR(P, H(IDd, RMd));
macro Q' = H(IDd, IDcs, Rcs', SKes-d', Tcs);
match (Q,Q'); # If the condition is true then the Cloud Server is authenticated and SKes-d is verified
macro RMj' = XOR(Bj, H(IDsj, Rj', Tj));
macro Aj' =H(IDsj, IDd, Rj', RMj, Tj);
match (Aj',Aj); # If the condition is true then the Sensor node is verified
fresh Rd: Nonce; # Rd is the random number
fresh SKs-d: Nonce;# SKs-d is a randomly chosen value
macro Cd = H(IDd, IDsj, Rd, SKs-d, LRj);
macro Ed = XOR(SKs-d, H(IDsj, RRj));
macro Fd = XOR(Rd, H(IDsj, LRj));
send_!4(Drone, Sensor, IDd, Cd, Ed, Fd);# sends values to the Sensor node
claim (Drone, Niagree); # Non-injective agreement
claim (Drone, Nisynch); #Non-injective synchronization
claim (Drone,Secret, SKs-d); # Checks whether the common key SKs-d is secret
claim (Drone,Secret, SKes-d); # Checks whether the common key SKes-d is secret

}

role Cloud
{
const Sc;
recv_!2(Drone, Cloud, IDd, L, N, Td );
const IDcs; #IDcs is the Cloud Server Identity
fresh Rcs: Nonce; # Rcs is a randomly chosen value
fresh SKes-d: Nonce; # SKes-d is randomly chosen
macro kd' = H(IDd, IDcs, SN, T);
macro RMd' = XOR(N, H(IDcs, Kd'));
macro L' = H(IDd, Kd', RMd', Td);
match (L', L); # If the condition is true then the Drone is registered and authenticated
macro P = XOR(Rcs, H(IDd, RMd'));
macro V = XOR(SKes-d, H(IDd, Kd', Tcs));
macro Q = H(IDd, IDcs, Rcs, SKes-d, Tcs);
send_!3(Cloud, Drone, P,Q,V,Tcs); # sends values to the Drone
claim(Cloud, Niagree); # Non-injective agreement
claim (Cloud, Nisynch); #Non-injective synchronization
claim_Cloud(Cloud,Secret, SKes-d); # Checks whether the common key SKes-d is secret
}
}

#CODE 2:
usertype Timestamp,PUF,SK; #SK : Secret Key
hashfunction H;
const XOR:Function;
const ADD:Function;
const MUL:Function;
const GEN:Function;
const  IDi, Pdi, Updi, Tcs,UAi, IDcs, SN, 
Udi, UEi, UFi, UGi, IDi', Pdi', Rui', UGi', 
URi', Updi',CRi', UKi, ULi, UNi,  RAN'', UKi'',
ULi'', UQ, UP, UW, SKu-cs'', RANcs'',RANcs,Tui ;                        
const ADD: Function;
protocol Major2(User,Cloud) #The code present the authentication procedure  between the User  and the Cloud Server
{
role User
{
fresh Rui,UCi: Nonce; # Rui, UCi is a randomly chosen value
var URi,CRi: Nonce;
var URi'':Nonce;
var RANcs,SKu-cs:Nonce;
macro Updi = H(Pdi, Rui);
send_!1(User,Cloud, IDi,Updi,UCi); # sends the concatenated values to the Cloud Server
recv_!2(Cloud,User,URi,UAi,CRi); # receives the concatenated values from the Cloud Server
macro UDi= XOR(URi,Pdi); 
macro UEi= XOR(CRi, H(IDi,Pdi));
macro UFi= XOR(Rui, H(XOR(IDi, Pdi,UCi)));
macro UGi= H(IDi,Pdi,Rui);
macro Rui'= XOR(UFi, H(XOR(IDi',Pdi',UCi)));
macro UGi'= H(IDi', Pdi', Rui');
match(UGi', UGi); #if the values matches then the User has provided the correct login credentials
fresh RAN:Nonce; # RAN is a randomly chosen value
macro URi'= XOR(Udi,Pdi');
macro Updi'= H(Pdi',Rui');
macro CRi'= XOR(UEi, H(IDi',Pdi'));
macro UKi= XOR(UAi,H(IDi',Updi',CRi'));
macro ULi=  H(IDi,UKi,CRi',RAN,Tui,URi');
macro UNi= XOR(RAN, H(IDcs,URi'));
send_!3(User,Cloud,IDi,UCi,ULi,UNi,Tui); # sends the concatenated values to the Cloud Server
recv_!4(Cloud,User, UQ,UP,UW,Tcs); # receives the concatenated values from the Cloud
macro SKu-cs''=XOR(UQ,H(IDi,URi,RAN));
macro RANcs''= XOR(UW,RAN);
macro RANcs'= {UP}SKu-cs'';
match (RANcs’’, RANcs’);#if the values matches then the Cloud server is authenticated 
                      #to the User, the session key is verified and the SKu-cs’’ = SKu-cs is the common session key
claim(User, Niagree); # Non-injective agreement
claim(User, Nisynch); #Non-injective synchronization
claim(User,Secret,Pdi); # Checks whether the common key Pdi is secret
claim(User,Secret,SKu-cs''); # Checks whether the common key SKu-cs is secret
}
role Cloud
{
const Sc,UCi,CRi;
const IDcs;
var Rui,UCi: Nonce;
var RAN:Nonce;
recv_!1(User, Cloud, IDi,Updi,UCi);
fresh URi,CRi: Nonce; # Uri, CRi is a randomly chosen value
macro UAi= XOR(H(IDcs, SN, UCi), H(IDi,Updi,CRi));
send_!2(Cloud,User,URi,UAi,CRi); # sends the concatenated values to the User
recv_!3(User,Cloud,IDi,UCi,ULi,UNi,Tui); # receives the concatenated values from the User
fresh URi'':Nonce; # URi’’ is a randomly chosen value
macro RAN''= XOR(UNi, H(IDcs,URi'')); 
macro UKi''= H(IDcs, SN, UCi);
macro ULi'= H(IDi'',UKi'',CRi, RAN'', Tui'', URi'');
match (ULi’’, ULi);#if the values matches then the User is authenticated to the Cloud Server
fresh RANcs,SKu-cs:Nonce; # RANcs, SKu-cs is a randomly chosen value
macro UQ= XOR(SKu-cs, H(IDi,URi,RAN''));
macro UP= {RANcs}SKu-cs;
macro UW= XOR(RANcs,RAN'');
send_!4(Cloud,User, UQ,UP,UW,Tcs); # sends the concatenated values to the User
claim(Cloud,Niagree); # Non-injective agreement
claim(Cloud,Nisynch); #Non-injective synchronization
claim(Cloud,Secret,SKu-cs); # Checks whether the common key SKu-cs is secret
}}
