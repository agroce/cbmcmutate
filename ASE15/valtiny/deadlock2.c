#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <assert.h>

pthread_mutex_t lock1 = PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t lock2 = PTHREAD_MUTEX_INITIALIZER;

int x;
int y;

void *f1(void *arg)
{
  pthread_mutex_lock(&lock1);
  x = x + 1;

  pthread_mutex_lock(&lock2);
  y = y + 1;
  pthread_mutex_unlock(&lock2);
  pthread_mutex_unlock(&lock1);
  pthread_exit(NULL);
} 

void *f2(void *arg)
{
  pthread_mutex_lock(&lock1);
  x = x + 1;
  pthread_mutex_lock(&lock2);
  y = y + 1;
  pthread_mutex_unlock(&lock2);
  pthread_mutex_unlock(&lock1);
  pthread_exit(NULL);
} 


int main(int argc, char *argv[])
{
	pthread_t t1;
	pthread_t t2;

	int join1, join2;

	x = 0;
	y = 0;

	if (pthread_create(&t1, NULL, f1, NULL))
		abort();
	if (pthread_create(&t2, NULL, f2, NULL))
		abort();

	join1 = pthread_join(&t1, NULL); 
	join2 = pthread_join(&t2, NULL); 

	printf("join1 = %d, join2 = %d\n",join1,join2);

	assert (join1 == 0);
	assert (join2 == 0);

}
