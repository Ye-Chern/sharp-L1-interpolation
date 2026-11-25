// Generate exact-integer interval certificates of H_n'(t)>0 on (0,1/2].
// Build: g++ -O3 -std=c++17 chebyshev_exact_certificate.cpp -o verify
// Run: ./verify 3 79
// All sign tests use integers. Floating point is used ONLY for untrusted
// initial root guesses and for printing approximate positive margins.
#include <array>
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <limits>
using I=std::int64_t;
using W=__int128_t;
constexpr I S=I(1)<<55; // all dyadic quantities represented in units 1/S
constexpr int MAX=90;
static void require(bool b,const char* what,int n,I t){
 if(!b){std::fprintf(stderr,"FAIL %s n=%d t=%lld/%lld\n",what,n,(long long)t,(long long)S);std::exit(1);}
}
// Fixed-point multiplication: exact integer truncation, error < 1 unit.
static I mul(I x,I y){return (I)((W)x*y/S);}
// Approximation to S*(U_{n+1}(y/S)-2(t/S)U_n(y/S)+(t/S)^2 U_{n-1}(y/S)).
// The Chebyshev recurrence's impulse response is U_j, with |U_j|<=j+1.
// Hence the error in each U_k is <=k(k-1)/2 units. The error here is
// < 4(n+3)^2 units, including the final three truncated multiplications.
static W p(int n,I t,I y){
 I a=S,b=2*y,c=0;
 for(int k=1;k<=n;k++){
  c=(I)((W)2*y*b/S)-a;
  if(k==n)break;
  a=b;b=c;
 }
 return (W)c-mul(2*t,b)+mul(t,mul(t,a));
}
// CDF of a uniform-simplex linear combination of sorted knots at zero.
// Positive convex-combination recurrence; all arithmetic is exact.
// up=true yields an upper bound in units 1/S; false a lower bound.
static std::array<I,4> cdf(const std::array<I,MAX>& a,int m,bool up){
 std::array<I,MAX> f{};for(int i=0;i<m;i++)f[i]=a[i]<=0?S:0;
 std::array<I,4> z{}; // core, plus endpoint, minus endpoint, both endpoints
 for(int k=1;k<m;k++){
  for(int i=0;i<m-k;i++){
   I l=a[i],h=a[i+k];
   if(h<=0)f[i]=S;
   else if(l>=0)f[i]=0;
   else {
    I d=h-l;W v=(W)(-l)*f[i]+(W)h*f[i+1];
    f[i]=(I)((v+(up?d-1:0))/d);
   }
  }
  if(k==m-3)z[0]=f[1];
  if(k==m-2){z[1]=f[1];z[2]=f[0];}
  if(k==m-1)z[3]=f[0];
 }
 return z;
}
struct Bounds{std::array<I,4> lo,hi;std::array<I,MAX> a,b;};
static Bounds evaluate(int n,I t){
 const int m=n+3;std::array<I,MAX> a{},b{};
 a[0]=b[0]=t-S;a[m-1]=b[m-1]=t+S;
 // The transcendental calculations here are NOT trusted by the certificate.
 double td=(double)t/(double)S,pi=std::acos(-1.0),q=(1+td)/(1-td);
 W err=4*(W)(n+3)*(n+3);
 for(int k=1;k<=n+1;k++){
  double th=k*pi/(n+2);
  for(int j=0;j<5;j++){
   double cs=std::cos(th),sn=std::sin(th);
   double phi=2*std::atan2(q*sn,1+cs);
   double der=n+1+(1-td*td)/(1-2*td*cs+td*td);
   th-=((n+1)*th+phi-k*pi)/der;
  }
  double yy=std::cos(th)*(double)S;
  require(std::isfinite(yy)&&std::abs(yy)<(double)S,"root guess",n,t);
  I y=(I)std::llround(yy),r=S>>40,l=0,h=0;bool ok=false;
  for(int j=0;j<12;j++){
   l=y-r;h=y+r;if(l< -S||h>S)break;
   W pl=p(n,t,l),ph=p(n,t,h);
   if((pl>err&&ph< -err)||(pl< -err&&ph>err)){ok=true;break;}
   r*=2;
  }
  require(ok,"root bracket",n,t);
  a[k]=t-h;b[k]=t-l;
  require(a[k]>b[k-1],"disjoint root intervals",n,t);
 }
 require(a[m-1]>b[m-2],"right endpoint",n,t);
 auto fa=cdf(a,m,true),fb=cdf(b,m,false);Bounds out;
 for(int i=0;i<4;i++){
  out.lo[i]=S-2*fa[i];out.hi[i]=S-2*fb[i];
  require(out.lo[i]<=out.hi[i],"CDF bounds",n,t);
 }
 out.a=a;out.b=b;return out;
}
// A rigorous lower bound for 2*S*H_n'(t), simultaneously for t in [a,b].
static W lower2(int n,const Bounds& a,const Bounds& b){
 return (W)a.lo[1]+a.lo[2]+(W)n*((W)a.lo[3]-b.hi[0]);
}
static void emit(FILE* f,int n,I t,const Bounds& b){
 if(!f)return;std::fprintf(f,"%d,%lld",n,(long long)t);
 for(int k=1;k<=n+1;k++)std::fprintf(f,",%lld,%lld",(long long)(t-b.b[k]),(long long)(t-b.a[k]));
 std::fputc('\n',f);
}
int main(int argc,char**argv){
 int n0=argc>1?std::atoi(argv[1]):3,n1=argc>2?std::atoi(argv[2]):19;
 FILE* f=argc>3?std::fopen(argv[3],"w"):nullptr;if(argc>3&&!f)return 2;
 if(n0<3||n1>79||n0>n1)return 2;
 long total=0;long double worst=1e9L,worstorigin=1e9L;int worstn=0;
 for(int n=n0;n<=n1;n++){
  I a=S>>24;Bounds ba=evaluate(n,a);emit(f,n,a,ba);
  // On [0,2^-24], |H'''| <= M (Fourier derivative bound in the proof).
  I M=6*(I)(n+1)*(n+3)*(n+4);W L=lower2(n,ba,ba);
  require(L*S>4*(W)M*a*a,"near zero",n,a);
  long double origin=(long double)L/(2*a)-2*(long double)M*a/S;
  worstorigin=std::min(worstorigin,origin);long count=0;long double margin=1e9L;
  while(a<S/2){
   I b=std::min(S/2,a+3*a/(2*n));Bounds bb;
   for(int tries=0;;tries++){
    require(tries<30&&b>a,"step",n,a);bb=evaluate(n,b);W l=lower2(n,ba,bb);
    if(l>0){margin=std::min(margin,(long double)l/(2*a));break;}
    b=a+(b-a)/2;
   }
   a=b;ba=bb;emit(f,n,a,ba);count++;
  }
  total+=count;if(margin<worst){worst=margin;worstn=n;}
  std::printf("n=%d intervals=%ld origin_margin=%.9Lg min_lower_over_left_t=%.9Lg\n",n,count,origin,margin);std::fflush(stdout);
 }
 if(f)std::fclose(f);
 std::printf("PASS n=%d..%d total=%ld min_origin=%.12Lg min_margin=%.12Lg worst_n=%d\n",n0,n1,total,worstorigin,worst,worstn);
}
