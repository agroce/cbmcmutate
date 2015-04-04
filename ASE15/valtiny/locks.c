#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <assert.h>

pthread_mutex_t lock1 = PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t lock2 = PTHREAD_MUTEX_INITIALIZER;

int x;

void *f1(void *arg)
{
  //  pthread_mutex_lock(&lock1);
  x = x + 1;  
  //  pthread_mutex_unlock(&lock1);
} 

void *f2(void *arg)
{
  pthread_mutex_lock(&lock1);
  x = x + 1;
  pthread_mutex_unlock(&lock1);
} 


int main(int argc, char *argv[])
{

	pthread_t t1;
	pthread_t t2;

	x = 1;

	if (pthread_create(&t1, NULL, f1, NULL))
		abort();
	if (pthread_create(&t2, NULL, f2, NULL))
		abort();

        if (pthread_join(t1, NULL))
	  abort();
        if (pthread_join(t2, NULL))
	  abort();


	assert (x == 3); 
}
